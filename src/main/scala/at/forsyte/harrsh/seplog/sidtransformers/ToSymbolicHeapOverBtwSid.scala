package at.forsyte.harrsh.seplog.sidtransformers

import at.forsyte.harrsh.entailment.TopLevelConstraint
import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.seplog.inductive._
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Renaming, Var}

object ToSymbolicHeapOverBtwSid extends HarrshLogging {

  def apply(sh: SymbolicHeap, predPrefix: String, underlyingSID: RichSid): (RichSid, TopLevelConstraint) = {
    val shSCCs = SplitIntoRootedComponents(sh, underlyingSID)
    logger.debug(s"Split $sh into rooted components ${shSCCs.mkString(", ")}")
    val (allNewPreds, topLevelCalls) = progressNormalformOfSCCs(shSCCs, predPrefix, underlyingSID)
    logger.debug(s"New query is ${TopLevelConstraint(topLevelCalls, Seq.empty)} w.r.t. new per-SCC predicates:\n${allNewPreds.mkString("\n")}")
    val startPred = topLevelCalls.head.name // Arbitrarily assign start pred (will never be used)
    val integratedSID = mergeIntoOneSid(underlyingSID, allNewPreds, startPred, sh)
    (integratedSID, TopLevelConstraint(topLevelCalls, Seq.empty))
  }

  private def progressNormalformOfSCCs(shSCCs: Seq[SymbolicHeap], predPrefix: String, underlyingSID: RichSid) = {
    if (shSCCs.size == 1) {
      val scc = shSCCs.head
        val (newPreds, call) = rootedShToProgressSid(shSCCs.head, predPrefix, underlyingSID)
        (newPreds, Seq(call))
    } else {
      val newPredsBySCC = shSCCs.zipWithIndex.map{
        case (rootedSh, i) => rootedShToProgressSid(rootedSh, predPrefix + i + "_", underlyingSID)
      }
      (newPredsBySCC.flatMap(_._1), newPredsBySCC.map(_._2))
    }
  }

  private def toCall(pred: String, rootedSh: SymbolicHeap): PredCall = {
    PredCall(pred, rootedSh.freeVars)
  }

  private def mergeIntoOneSid(originalSID: RichSid, allNewPreds: Seq[(Predicate,Option[FreeVar])], startPred: String, originalSh: SymbolicHeap): RichSid = {
    val allPreds = originalSID.preds ++ allNewPreds.map(_._1)
    val allRoots = originalSID.roots ++ allNewPreds.filter(_._2.nonEmpty).map(pair => pair._1.head -> pair._2.get)
    RichSid(startPred, allPreds, description = s"SID for SCC decomposition of $originalSh", allRoots)
  }

  def rootedShToProgressSid(sh: SymbolicHeap, predPrefix: String, underlyingSID: RichSid): (Seq[(Predicate,Option[FreeVar])], PredCall) = {
    if (sh.pointers.isEmpty && sh.pure.isEmpty && sh.predCalls.size == 1 && sh.boundVars.isEmpty && !sh.usesNull) {
      // No need to introduce any new predicates
      (Seq.empty, sh.predCalls.head)
    } else {
      val TransformationResult(headPred, otherPreds) = introduceOnePredPerPointer(sh, predPrefix)
      logTransformationResult(headPred +: otherPreds)
      val normalizedHeadPred = normalizeHeadPred(headPred, underlyingSID)
      val newPreds = normalizedHeadPred +: otherPreds
      val newRoots = newPreds map { pred =>
        val from = pred.rules.head.body.pointers.headOption.map(_.from).filter(_.isFree)
        from.map(_.asInstanceOf[FreeVar])
      }
      val call = toCall(predPrefix + "1", sh)
      (newPreds zip newRoots, call)
    }
  }

  private def logTransformationResult(preds: Seq[Predicate]): Unit = {
    logger.debug(s"Transformation results:")
    for (pred <- preds) {
      logger.debug(s"Introducing pred ${pred.head} with free vars ${pred.rules.head.body.freeVars}, atoms ${pred.rules.head.body.atoms}, body ${pred.rules.head.body}")
      logger.debug(s"Overall: $pred")
    }
  }

  private def normalizeHeadPred(headPred: Predicate, underlyingSID: RichSid): Predicate = {
    assert(headPred.rules.size == 1)
    val rule = headPred.rules.head
    val body = rule.body
    if (body.hasPointer || body.predCalls.isEmpty) {
      // Progress satisfied => no further normalization necessary
      headPred
    } else {
      // Extract rules of an arbitrary pred call to establish progress
      val fstCall = body.predCalls.head
      val ruleBodies = underlyingSID(fstCall.name).bodySHs
      val instantiatedBodies = ruleBodies map (body.replaceCall(fstCall, _))
      val newRules = instantiatedBodies map SidFactory.shToRuleBody
      val res = Predicate(headPred.head, newRules)
      logger.debug(s"Normalizing rule ${headPred.head} <= $rule by replacing $fstCall with rules of ${fstCall.name}:\n$res")
      res
    }
  }

  case class TransformationResult(headPredicate: Predicate, otherPredicates: Seq[Predicate])

  private def introduceOnePredPerPointer(intermediateSh: SymbolicHeap, predPrefix: String, introducedPredicates: Seq[Predicate] = Seq.empty): TransformationResult = {
    val currName = predPrefix + (introducedPredicates.size + 1)
    val successorName = predPrefix + (introducedPredicates.size + 2)
    intermediateSh.pointers.size match {
      case 0 =>
        // No local allocation at all;
        // Simply introduce a single new predicate for this
        // Note that this will lead to special treatment in the automaton transitions, because progress is violated
        assert(introducedPredicates.isEmpty)
        TransformationResult(Predicate(currName, Seq(SidFactory.shToRuleBody(intermediateSh))), Seq.empty)
      case 1 =>
        // Exactly one pointer => Progress is satisfied => Simply create a single predicate
        val allPreds = introducedPredicates :+ Predicate(currName, Seq(SidFactory.shToRuleBody(intermediateSh)))
        TransformationResult(allPreds.head, allPreds.tail)
      case n if n >= 2 =>
        // Recurse on an arbitrary pointer
        val localPtr = intermediateSh.pointers.head
        val SplitResult(remainder, droppedFreeVars, newFreeVarsByBoundVar) = splitOffPtrAndAllPureAtoms(localPtr, intermediateSh)
        val recPredName = successorName
        val recPredParams = intermediateSh.freeVars.filterNot(droppedFreeVars.contains) ++ newFreeVarsByBoundVar.map(_._1)
        val recPredCall = PredCall(recPredName, recPredParams)
        val ruleSh = SymbolicHeap(pure = intermediateSh.pure,
          pointers = Seq(localPtr),
          predCalls = Seq(recPredCall),
          freeVars = intermediateSh.freeVars)
        val newPred = Predicate(currName, Seq(SidFactory.shToRuleBody(ruleSh)))
        introduceOnePredPerPointer(remainder, predPrefix, introducedPredicates :+ newPred)
    }
  }

  private case class SplitResult(newSh: SymbolicHeap, droppedFreeVars: Set[FreeVar], newFreeVarsByBoundVar: Seq[(BoundVar,Var)])

  /**
    * Return sh after removing atom. Any bound var shared between ptr/pure atoms and sh is turned into a fresh free var.
    */
  private def splitOffPtrAndAllPureAtoms(ptr: PointsTo, sh: SymbolicHeap): SplitResult = {
    val pureAtoms = sh.pure
    val splitOffBoundVars = Var.boundVars(ptr.getNonNullVars ++ pureAtoms.flatMap(_.getNonNullVars))
    val remainderAtoms = sh.pointers.filterNot(_ == ptr) ++ sh.predCalls
    val remainder = SymbolicHeap(remainderAtoms:_*)

    // All bound vars that are shared between the two parts must become parameters of the new predicate...
    val sharedBoundVars = (splitOffBoundVars intersect remainder.boundVars).toSeq
    // ...whereas free vars that don't occur in the part of the splitting won't become parameters of the new predicate...
    val droppedFreeVars = sh.freeVars.filterNot(remainder.freeVars.contains).toSet
    // ...leading to the following renaming of free/bound vars to the new uninterrupted sequence of free vars:
    val freeVarNamesForRemainder = Var.freshFreeVars(Set.empty, remainder.freeVars.size + sharedBoundVars.size)
    val renamingMap: Map[Var,Var] = (remainder.freeVars ++ sharedBoundVars).lazyZip(freeVarNamesForRemainder).toMap
    val renaming = Renaming.fromMap(renamingMap)
    val renamedRemainder = remainder.rename(renaming, overrideFreeVars = Some(freeVarNamesForRemainder))

    // Close gaps in resulting bound variable sequence
    // TODO: The SH API is obviously not meant to be used in this way. Refactor?
    val normalizedRemainder = SymbolicHeap(renamedRemainder.atoms.closeGapsInBoundVars, renamedRemainder.freeVars)

    logger.debug(s"Splitting off $ptr and pure atoms from $sh: Got $remainder, renamed to $renamedRemainder, normalized to $normalizedRemainder")
    val newFreeVarsByBoundVar = sharedBoundVars.map(bv => (bv,renamingMap(bv)))
    SplitResult(normalizedRemainder, droppedFreeVars, newFreeVarsByBoundVar)
  }


}
