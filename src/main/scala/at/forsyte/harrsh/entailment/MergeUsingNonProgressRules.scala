package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.pure.Closure
import at.forsyte.harrsh.seplog.{BoundVar, Var}
import at.forsyte.harrsh.seplog.inductive._
import at.forsyte.harrsh.util.Combinators

object MergeUsingNonProgressRules extends HarrshLogging {

  // TODO: Simplify application of non-progress rules to profiles?

  def apply(profile: EntailmentProfile, sid: RichSid): EntailmentProfile = profile match {
    case p: ProfileOfNondecomposableModels => p
    case p: ProfileOfDecomps => mergeDecomps(p, sid)
  }

  def mergeDecomps(profile: ProfileOfDecomps, sid: RichSid): EntailmentProfile = {
    if (sid.empClosedNonProgressRules.isEmpty) {
      profile
    } else {
      logger.debug("Will try to apply non-progress rules to non-empty decompositions in " + profile)
      val newDecomps = for {
        decomp <- profile.decomps
        merged <- if (decomp.isEmpty) Seq(decomp) else useNonProgressRulesToMergeContexts(decomp, sid)
      } yield merged
      ProfileOfDecomps(newDecomps, profile.sharedConstraints, profile.params)
    }
  }

  def useNonProgressRulesToMergeContexts(decomp: ContextDecomposition, sid: RichSid): Seq[ContextDecomposition] = {
    val nonProgressRules = sid.empClosedNonProgressRules
    logger.debug(s"Will try to apply non-progress rules to contexts in decomposition\n$decomp.\nRules to consider: ${nonProgressRules.map(pair => s"${pair._1.defaultCall} <= ${pair._2}")}")
    mergeWithZeroOrMoreRuleApplications(decomp, nonProgressRules, sid)
  }

  private def mergeWithZeroOrMoreRuleApplications(decomp: ContextDecomposition, rules: Set[(Predicate, RuleBody)], sid: RichSid): Seq[ContextDecomposition] = {
    decomp +: applyAllPossibleRulesInMerge(decomp, rules).flatMap(mergeWithZeroOrMoreRuleApplications(_, rules, sid))
  }

  private def applyAllPossibleRulesInMerge(decomp: ContextDecomposition, rules: Set[(Predicate, RuleBody)]): LazyList[ContextDecomposition] = {
    rules.flatMap(rule => applyRuleInMerge(decomp, rule._2, rule._1)).to(LazyList)
  }

  private def applyRuleInMerge(decomp: ContextDecomposition, rule: RuleBody, pred: Predicate): Option[ContextDecomposition] = {
    assert(!rule.hasPointer)
    val decompBoundVars = decomp.boundVars.map(_.asInstanceOf[BoundVar])
    val shiftedRule = if (decompBoundVars.nonEmpty) {
      val shiftedBody = SymbolicHeap(rule.body.atoms.shiftBoundVars(rule.body.boundVars, decompBoundVars.max.index + 1), rule.body.freeVars)
      logger.debug(s"Shifted rule body from ${rule.body} to $shiftedBody to avoid clashing bound vars")
      rule.copy(body = shiftedBody)
    } else {
      rule
    }
    val callsInRule = shiftedRule.body.predCalls
    val roots = decomp.parts map (_.root)
    if (callsInRule.size > roots.size) {
      // The rule contains more calls than the decomposition has parts => Rule can't be applicable
      None
    } else {
      // FIXME: More efficient choice of possible pairings for matching (don't brute force over all seqs)
      val possibleMatchings = Combinators.allSeqsWithoutRepetitionOfLength(callsInRule.length, roots)
      possibleMatchings.flatMap(tryMergeGivenRoots(decomp, shiftedRule, pred, _)).headOption
    }
  }

  private def tryMergeGivenRoots(decomp: ContextDecomposition, rule: RuleBody, pred: Predicate, rootsToMerge: Seq[ContextPredCall]): Option[ContextDecomposition] = {
    val callsInRule = rule.body.predCalls
    assert(rootsToMerge.size == callsInRule.size)
    if (predicatesMatch(callsInRule, rootsToMerge)) {
      tryArgumentMatching(decomp, rule, pred, rootsToMerge)
    }
    else {
      None
    }
  }

  private def predicatesMatch(calls: Seq[PredCall], labels: Seq[ContextPredCall]): Boolean = {
    calls.lazyZip(labels).forall {
      case (call, label) => call.name == label.pred.head
    }
  }

  private def tryArgumentMatching(decomp: ContextDecomposition, rule: RuleBody, pred: Predicate, rootsToMerge: Seq[ContextPredCall]): Option[ContextDecomposition] = {
    val callsInRule = rule.body.predCalls
    val candidateMatching = callsInRule zip rootsToMerge
    val assignmentsByVar: Map[Var, Set[Set[Var]]] = varAssignmentFromMatching(candidateMatching)
    assignmentsByVar.find(_._2.size >= 2) match {
      case Some(pair) =>
        // FIXME: Do we have to implement speculative merging where we match even if we have duplicate targets, but record this as missing equality constraint in the pure constraints of the resulting decomposition?
        logger.debug(s"Can't match ${rule.body} against $rootsToMerge: ${pair._1} has to be assigned to all of ${pair._2.mkString(", ")}")
        None
      case None =>
        logger.debug(s"Will put contexts rooted in ${rootsToMerge.mkString(",")} under new root node labeled by ${pred.head}")
        mergeRoots(decomp, rootsToMerge, rule, pred, assignmentsByVar.view.mapValues(_.head).toMap)
    }
  }

  private def varAssignmentFromMatching(matched: Seq[(PredCall, ContextPredCall)]) = {
    val varAssignmentSeq = for {
      (call, root) <- matched
      (arg, varLabel) <- call.args.lazyZip(root.subst.toSeq)
    } yield (arg, varLabel)
    val assignmentsByVar: Map[Var, Set[Set[Var]]] = varAssignmentSeq.groupBy(_._1).map {
      case (k, vs) => (k, vs.map(_._2).toSet)
    }
    assignmentsByVar
  }

  private def mergeRoots(decomp: ContextDecomposition, rootsToMerge: Seq[ContextPredCall], rule: RuleBody, pred: Predicate, assignmentsByVar: Map[Var, Set[Var]]): Option[ContextDecomposition] = {
    assume(decomp.boundVars.intersect(rule.body.boundVars.toSet).isEmpty)
    val (ctxsToMerge, unchangedCtxs) = decomp.parts.partition(ctx => rootsToMerge.contains(ctx.root))
    logger.debug(s"Roots that were matched: $rootsToMerge")
    logger.debug(s"Will apply $rule to merge:\n${ctxsToMerge.mkString("\n")}")
    logger.debug(s"Merge based on variable assignment $assignmentsByVar")
    val closureOfRule = Closure.ofAtoms(rule.body.pure)
    val lookup = (v: Var) => {
      val lookedUp = for {
        // Because of possible aliasing with bound variables, it's not enoough to simply look up the free var v in the assignment
        // We must look up everything equivalent to the free var v
        eq <- closureOfRule.getEquivalenceClass(v)
        assigned <- assignmentsByVar.getOrElse(eq, Set.empty)
      } yield assigned
      // Not all variables of the rule need to be involved in the matching, that's why we must supply default targets
      if (lookedUp.nonEmpty) lookedUp else decomp.constraints.classOf(v)
    }
    val subst = Substitution(rule.body.freeVars map lookup)
    logger.debug(s"Computed substitution $subst")
    val newRoot = ContextPredCall(pred, subst)
    val concatenatedLeaves = ctxsToMerge.flatMap(_.calls)
    val ctxAfterMerging = EntailmentContext(newRoot, concatenatedLeaves)
    val newCtxs = unchangedCtxs + ctxAfterMerging
    val occurringLabels = newCtxs.flatMap(_.classes)
    val ruleBoundVars = rule.body.boundVars.toSet[Var]
    val classesForNewBoundVars = ruleBoundVars map (Set(_))

    for {
      restrictedConstraints <- decomp.constraints.restrictToNonPlaceholdersAnd(occurringLabels)
      mergedDecomp = ContextDecomposition(newCtxs, restrictedConstraints)
      // Since the fresh bound vars aren't used in any way, we can actually discard speculative equalities that use them
      // FIXME: What about speculative disequalities?
      speculationUpdate = SpeculativeUpdate(rule.body.pure, mergedDecomp.constraints.classes ++ classesForNewBoundVars, assumeWithoutSpeculation = ruleBoundVars)
      withSpeculation <- mergedDecomp.updateSubst(speculationUpdate)
      finalDecomp <- if (ruleBoundVars.nonEmpty) withSpeculation.forget(ruleBoundVars) else Some(withSpeculation)
    } yield finalDecomp.toPlaceholderNormalForm
  }

}
