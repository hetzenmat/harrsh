package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.seplog.Var
import at.forsyte.harrsh.seplog.inductive.{SID, SIDUnfolding, SymbolicHeap}
import at.forsyte.harrsh.util.Combinators

import scala.annotation.tailrec

/**
  * Created by jens on 3/6/17.
  */
object GenerateEntailmentAutomata extends HarrshLogging {

  def apply(maxNumFV : Int, sid : SID, reportProgress : Boolean = false) : EntailmentHeapAutomaton = {

    val ecds = new ECDComputation(sid, maxNumFV, reportProgress = reportProgress).run()
    if (reportProgress) println("Finished ECD computation. Found " + ecds.size + " classes.")

    // TODO Symmetry, null parameters etc.

    // TODO Should of course do this on the fly while computing the ECDs...
    val stateDescriptors = for {
      (r,e) <- ecds
      entailsP = GreedyUnfoldingModelChecker.reducedEntailmentAsModelChecking(r, sid.callToStartPred, sid)
    } yield (r,e,entailsP)

    for {
      (r,e,f) <- stateDescriptors
    } {
      println("representative: " + r + " extension: " + e + " final: " + f)
    }

    new EntailmentHeapAutomaton(maxNumFV, stateDescriptors)
  }

  /**
    * Equivalence class descriptors
    */
  type ECD = (SymbolicHeap, SymbolicHeap)

  private class ECDComputation(sid : SID, maxNumFv : Int, reportProgress : Boolean) {

    // TODO Pure formula treatment: Should probably look just at spatial part of partitions and keep track of pure part separately (tracking)? But then have to modify the reduced entailment check?

    def FindOnlyNonEmpty = true // Only generate non-empty left-hand sides. Still have to figure out if this is the right approach

    def run(): Seq[ECD] = {
      ecdIteration(1, Seq.empty, Seq(sid.callToStartPred))
    }

    private def ecdIteration(i: Int, ecdPrev: Seq[ECD], partialUnfoldings: Seq[SymbolicHeap]): Seq[ECD] = {

      def printProgress(msg: String): Unit = if (reportProgress) println("Iteration " + i + ": " + msg)

      printProgress("Starting new iteration; ECDs so far: " + ecdPrev.mkString(", "))
      printProgress("Will unfold the following formulas:\n" + partialUnfoldings.map(" - " + _).mkString("\n"))

      val nextUnfs = SIDUnfolding.unfoldOnce(sid, partialUnfoldings)
      val (reducedUnfs, newPartialUnfs) = nextUnfs.partition(_.predCalls.isEmpty)
      printProgress("Reduced unfs for current iteration:\n" + reducedUnfs.map(" - " + _).mkString("\n"))
      printProgress("Non-reduced unfs for next iteration:\n" + newPartialUnfs.map(" - " + _).mkString("\n"))

      printProgress("Old ECDs: " + ecdPrev.size + "; Partial lvl. i-1 unfs.: " + partialUnfoldings.size + "; Lvl. i reduced/non-reduced unfs.: " + reducedUnfs.size + "/" + newPartialUnfs.size)

      val ecdNew = processUnfoldings(reducedUnfs, ecdPrev, printProgress)

      if (!ecdPrev.isEmpty && ecdNew.size == ecdPrev.size) {
        // If we've already found at least one ECD, but now don't find a new one, we terminate
        val termMsg = "ECD computation reached fixed point";
        logger.debug(termMsg);
        printProgress(termMsg)
        ecdPrev
      } else {
        // Found at least one new ECD => recurse
        printProgress("Found " + ecdNew.size + " new ECDs");
        logger.debug("Iteration " + i + ": Found " + ecdNew.size + " new ECDs")
        ecdIteration(i + 1, ecdPrev ++ ecdNew, newPartialUnfs)
      }
    }

    @tailrec private def processUnfoldings(reducedUnfs : Seq[SymbolicHeap], ecdAcc : Seq[ECD], printProgress : String => Unit) : Seq[ECD] = {
      if (reducedUnfs.isEmpty) ecdAcc else {
        printProgress("Processing Unfolding: " + reducedUnfs.head)
        val candidates = partitions(reducedUnfs.head)
        printProgress("Partitions with " + (if (FindOnlyNonEmpty) "(non-empty)" else "(possibly empty)") + " left part to consider: " + candidates.size)
        val ecdAccwithEcdsForUnfolding = processPartitions(candidates, ecdAcc, printProgress)
        processUnfoldings(reducedUnfs.tail, ecdAccwithEcdsForUnfolding, printProgress)
      }
    }

    @tailrec private def processPartitions(candidates : Set[ECD], ecdAcc : Seq[ECD], printProgress : String => Unit) : Seq[ECD] = {
      if (candidates.isEmpty) ecdAcc else {
        val ecd = candidates.head
        printProgress("Processing Partition: " + ecd)
        val newAcc = if (!ecdAcc.contains(ecd) && isNew(ecdAcc, ecd, printProgress)) {
          printProgress("*** New ECD " + ecd + " ***")
          ecdAcc :+ ecd
        } else {
          printProgress("=> " + ecd + " assumed equal to previous ECD.")
          ecdAcc
        }

        processPartitions(candidates.tail, newAcc, printProgress : String => Unit)
      }
    }

    @tailrec private def isNew(oldECDs: Seq[ECD], candidate: ECD, printProgress : String => Unit): Boolean = if (oldECDs.isEmpty) {
      true
    } else {
      val (hd, tl) = (oldECDs.head, oldECDs.tail)
      printProgress("Comparing against " + hd)
      val notNew = areBiExtensible(hd, candidate, printProgress)
      if (notNew) false else isNew(tl, candidate, printProgress)
    }

    private def areBiExtensible(fst: ECD, snd: ECD, printProgress : String => Unit): Boolean = {
      val fstExt = SymbolicHeap.combineHeaps(fst._1, snd._2)
      val fstRes = reducedEntailment(fstExt, sid.callToStartPred)
      printProgress("Checking 1st extension " + fst._1 + " * " + snd._2 + " |?= " + sid.callToStartPred + " ---> " + fstRes)
      if (fstRes) {
        val sndExt = SymbolicHeap.combineHeaps(snd._1, fst._2)
        val sndRes = reducedEntailment(sndExt, sid.callToStartPred)
        printProgress("Checking 2nd extension " + snd._1 + " * " + fst._2 + " |?= " + sid.callToStartPred + " ---> " + sndRes)
        sndRes
      } else {
        false
      }
    }

    private def partitions(rsh: SymbolicHeap): Set[ECD] = {
      for {
        sigma1 <- Combinators.powerSet(rsh.pointers.toSet)
        // TODO Separate handling of emp?
        if FindOnlyNonEmpty && !sigma1.isEmpty
        pi1 <- Combinators.powerSet(rsh.pure.toSet)
        // TODO Powerset computation that returns subsets together with their complements
        sigma2 = rsh.pointers.toSet -- sigma1
        pi2 = rsh.pure.toSet -- pi1
        representative = SymbolicHeap(pi1.toSeq, sigma1.toSeq, Seq.empty)
        extension = SymbolicHeap(pi2.toSeq, sigma2.toSeq, Seq.empty)
        // FIXME Must consider all ways to name the new FVs in the representative...
        repWithExtPoints = unbindShared(representative, extension)
        if repWithExtPoints.numFV <= maxNumFv
        extWithExtPoints = unbindShared(extension, representative)
      } yield (repWithExtPoints, extWithExtPoints)
    }

    private def unbindShared(rshToModify : SymbolicHeap, sharedWith : SymbolicHeap) : SymbolicHeap = {
      def unbindAll(vars : Seq[Var], sh : SymbolicHeap) : SymbolicHeap = if (vars.isEmpty) sh else {
        val nextSH = sh.instantiateBoundVar(vars.head, sh.numFV+1)
        unbindAll(vars.tail, nextSH)
      }

      val sharedVars = rshToModify.boundVars.toSet intersect sharedWith.boundVars.toSet
      // FIXME Actually should consider all ways to order the FVs? See also the comment above
      unbindAll(sharedVars.toSeq, rshToModify)
    }

    private def reducedEntailment(lhs: SymbolicHeap, rhs: SymbolicHeap) : Boolean = GreedyUnfoldingModelChecker.reducedEntailmentAsModelChecking(lhs, rhs, sid, reportProgress)

  }

}
