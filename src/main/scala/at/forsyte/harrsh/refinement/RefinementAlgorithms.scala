package at.forsyte.harrsh.refinement

import java.text.SimpleDateFormat

import at.forsyte.harrsh.heapautomata._
import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.seplog.Var._
import at.forsyte.harrsh.seplog.inductive._
import at.forsyte.harrsh.seplog.{PtrExpr, Var}
import at.forsyte.harrsh.util.IOUtils

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.concurrent.duration.Duration

/**
  * Created by jens on 10/15/16.
  */

object RefinementAlgorithms {

  /**
    * On the fly refinement, stopping as soon as non-emptiness of the (partially) refined is disocvered.
    * @param sid SID to refine
    * @param ha Automaton by which we refine
    * @param reportProgress Periodically report the number of iterations
    * @return
    */
  def onTheFlyRefinementWithEmptinessCheck(sid : SID, ha : HeapAutomaton, reportProgress : Boolean) : Boolean = {
    RefinementInstance(sid, ha).onTheFlyEmptinessCheck(reportProgress)
  }

  /**
    * Refines SID
    * @param sid The SID to refine
    * @param ha Automaton by which we refine
    * @param timeout Return None after this timeout has passed
    * @param reportProgress Periodically report the number of iterations
    * @return The refined SID + emptiness flag (true iff empty) or None in case of timeout
    */
  def refineSID(sid: SID, ha: HeapAutomaton, timeout: Duration, reportProgress: Boolean): Option[(SID,Boolean)] = {
    val f: Future[(SID,Boolean)] = Future {
      RefinementInstance(sid, ha).refineSID(reportProgress = reportProgress)
    }

    try {
      val sid = Await.result(f, timeout)
      Some(sid)
    } catch {
      case e: TimeoutException =>
        println("reached timeout (" + timeout + ")")
        None
    }
  }

  /**
    * (Task to perform, is refined SID empty (or None if timeout), witness if nonempty)
   */
  type AnalysisResult = (AutomatonTask, Option[Boolean], Option[SymbolicHeap])

  def performFullAnalysis(sid: SID, numFV : Int, timeout: Duration): Unit = {

    val tasks : Seq[AutomatonTask] = Seq(RunSat(), RunUnsat(), RunEstablishment(), RunNonEstablishment(), RunMayHaveGarbage(), RunGarbageFreedom(), RunWeakAcyclicity(), RunStrongCyclicity())

    println("Beginning analysis...")
    val results : Seq[AnalysisResult] = for (task <- tasks) yield analyze(task, sid, numFV, timeout)
    println("Finished analysis.")
    println()

    // TODO Abstract printing result tables into its own function? (Compare Benchmarking.printBenchmarkResults)
    println("Analysis results for: " + sid)
    println()

    val shCol : Int = Math.max(40, results.map(_._3.toString.length).max - 5)
    val cols = Seq(20,20,shCol)
    val headings = Seq("Property", "Result", "Witness")
    val entries : Seq[Seq[String]] = for {
      (task,res,witness) <- results
    } yield Seq(task.toString, res.map(task.resultToString).getOrElse("TO"), witness.map(_.toString).getOrElse("-"))
    println(IOUtils.toTable(headings, cols, entries))

  }

  private def analyze(task : AutomatonTask, sid : SID, numFV : Int, timeout : Duration) : AnalysisResult = {
    val refined = refineSID(sid, task.getAutomaton(numFV), timeout, reportProgress = false)
    refined match {
      case None =>
        println(task + " did not finish within timeout (" + timeout.toSeconds + "s)")
        (task, None, None)
      case Some((refinedSid,empty)) =>
        println("Finished " + task + ": " + task.resultToString(empty))

        val witness : Option[SymbolicHeap] = if (!empty) {
          val w = SIDUnfolding.firstReducedUnfolding(refinedSid)
          //println("Witness: " + w)
          Some(w)
        } else {
          None
        }

        (task, Some(empty), witness)
    }
  }


  /**
    *
    * @param sid
    * @param ha
    */
  private case class RefinementInstance(sid : SID, ha : HeapAutomaton) extends HarrshLogging {

    /**
      * Mapping from src, label and head predicate to target state for reconstructing the full assignment
      */
    private var combinationsToTargets : Map[(Seq[ha.State],SymbolicHeap,String), Set[ha.State]] = Map.empty
    private var reachedFinalStates : Set[ha.State] = Set.empty

    /**
      * Refine the given SID
      * @param reportProgress Regularly print info about current iteration
      * @return The refined SID as well as a flag indicating whether it is empty
      */
    def refineSID(reportProgress : Boolean) : (SID,Boolean) = {

      val (empty, reach) = computeRefinementFixedPoint(sid.startPred, computeFullRefinement = true, reportProgress = reportProgress)(Set(), Set(), 1)

      // Assign suffixes to each state
      val states : Set[ha.State] = (for ((states, _, _, headState) <- reach) yield states :+ headState).flatten
      val stateToIndex : Map[ha.State, Int] = Map() ++ states.toSeq.zipWithIndex

      val innerRules = for {
        (states,body,head,headState) <- reach.toSeq
      } yield Rule(
        head = head+stateToIndex(headState),
        freeVars = body.freeVars map Var.toDefaultString,
        qvars = body.boundVars.toSeq map Var.toDefaultString,
        body = SymbolicHeap.addTagsToPredCalls(body, states map (s => ""+stateToIndex(s))))
      val finalRules = reachedFinalStates.toSeq.map{
        state =>
          Rule(
            head = sid.startPred,
            freeVars = (1 to sid.arityOfStartPred) map Var.toDefaultString,
            qvars = Seq(),
            body = SymbolicHeap(Seq.empty, Seq(PredCall(sid.startPred+stateToIndex(state), (1 to sid.arityOfStartPred) map mkVar map PtrExpr.fromFV))))
      }

      if (reachedFinalStates.isEmpty) {
        logger.info("Refined SID is empty")
      }

      (SID(
        startPred = sid.startPred,
        rules = innerRules ++ finalRules,
        description = "Refinement of " + sid.description + " with " + ha.description,
        numFV = sid.numFV
      ), reachedFinalStates.isEmpty)
    }

    /**
      * @return True iff there is no RSH in the refinement of sid by ha
      */
    def onTheFlyEmptinessCheck(reportProgress : Boolean) : Boolean = {
      computeRefinementFixedPoint(sid.startPred, computeFullRefinement = false, reportProgress = reportProgress)(Set(), Set(), 1)._1
    }

    @tailrec
    private def computeRefinementFixedPoint(pred : String, computeFullRefinement : Boolean, reportProgress : Boolean)(r : Set[(String, ha.State)], previousCombinations : Set[(Seq[ha.State],SymbolicHeap,String)], iteration : Int) : (Boolean,Set[(Seq[ha.State],SymbolicHeap,String,ha.State)]) = {
      // TODO The refinment fixed point computation is quite long and convoluted now. Cleanup

      def reachedStatesForPred(rel : Set[(String, ha.State)], call : String) : Set[ha.State] = rel filter (_._1 == call) map (_._2)

      def allDefinedSources(rel : Set[(String, ha.State)], calls : Seq[String]) : Set[Seq[ha.State]] = {
        if (calls.isEmpty) {
          Set(Seq())
        } else {
          for {
            tail <- allDefinedSources(rel, calls.tail)
            head <- reachedStatesForPred(rel, calls.head)
          } yield head +: tail
        }
      }

      def performSingleIteration: Seq[((String, ha.State), (Seq[ha.State],SymbolicHeap,String))] = {
        if (ha.implementsTargetComputation) {
          for {
            Rule(head, _, _, body) <- sid.rules
            src <- {
              val srcs  = allDefinedSources(r, body.identsOfCalledPreds)
              logger.debug("Looking at defined sources for " + head + " <= " + body + "; found " + srcs.size)
              srcs
            }
            // Only go on if we haven't tried this combination in a previous iteration
            if {
              logger.debug("Computing targets for " + head + " <= " + body + " from source " + src + " ?")
              !previousCombinations.contains((src, body, head))
            }
            trg <- {
              logger.debug("Yes, targets not computed previously, get targets for " + body)
              ha.getTargetsFor(src, body)
            }
          } yield ((head, trg), (src,body,head))
        } else {
          // No dedicated target computation, need to brute-force
          for {
            Rule(head, _, _, body) <- sid.rules
            src <- allDefinedSources(r, body.identsOfCalledPreds)
            // Only go on if we haven't tried this combination in a previous iteration
            if !previousCombinations.contains((src, body, head))
            // No smart target computation, have to iterate over all possible targets
            trg <- ha.states
            if ha.isTransitionDefined(src, trg, body)
          } yield ((head, trg), (src,body,head))
        }
      }

      def isFinal(pair : (String,ha.State)) : Boolean = pair._1 == pred && ha.isFinal(pair._2)

      if (computeFullRefinement && iteration == 1) {
        // Reset state
        combinationsToTargets = Map.empty
        reachedFinalStates = Set.empty
      }

      val discoveredStartPredicate = r.find(isFinal)
      if (discoveredStartPredicate.isDefined && computeFullRefinement) {
        // Save reached final states for generation of refined SID
        reachedFinalStates = reachedFinalStates ++ r.filter(isFinal).map(_._2)
      }

      if (discoveredStartPredicate.isDefined && !computeFullRefinement) {
        // There is a derivation that reaches a final state, refined language nonempty
        // We only continue the fixed-point computation if we're interested in the full refinement; otherwise we return false
        logger.debug("Reached " + discoveredStartPredicate.get + " => language is non-empty")
        (false, Set.empty)
      } else {
        logger.debug("Beginning iteration #" + iteration)
        val iterationResult = performSingleIteration
        val (newPairs, newCombs) = iterationResult.unzip
        val union = r ++ newPairs

        if (computeFullRefinement) {
          // In the computation of the full refinement, we must remember the targets of each of the combinations we tried
          val kvPairs = iterationResult map {
            case ((_,trg),comb) => (comb,trg)
          }
          for ((k,v) <- kvPairs) {
            if (combinationsToTargets.isDefinedAt(k)) {
              combinationsToTargets = combinationsToTargets + (k -> (combinationsToTargets(k) + v))
            } else {
              combinationsToTargets = combinationsToTargets + (k -> Set(v))
            }
          }
        }

        logger.debug("Refinement iteration: #" + iteration + " " + (if (newPairs.isEmpty) "--" else newPairs.mkString(", ")))
        if (reportProgress) println(dateFormat.format(new java.util.Date()) + " -- Refinement iteration: #" + iteration + " Discovered " + newPairs.size + " targets; total w/o duplicates: " + union.size)

        if (union.size == r.size) {
          // Fixed point reached without reaching a pred--final-state pair
          logger.debug("Fixed point: " + union.mkString(", "))
          if (discoveredStartPredicate.isEmpty) {
            logger.debug("=> Language is empty")
          }
          // Only compute the new combinations + mapping to targets if desired (i.e., if full refinement was asked for)
          // (to save some computation time in the cases where we're only interested in a yes/no-answer)
          (true, if (computeFullRefinement) (previousCombinations ++ newCombs).flatMap(t => combinationsToTargets(t) map (trg => (t._1,t._2,t._3,trg))) else Set.empty)
        } else {
          // Fixed point not yet reached, recurse
          val unionOfPrevs = previousCombinations ++ newCombs
          computeRefinementFixedPoint(pred, computeFullRefinement, reportProgress)(union, unionOfPrevs, iteration + 1)
        }
      }
    }

    private lazy val dateFormat : SimpleDateFormat = new SimpleDateFormat("hh:mm:ss.SSS")

  }

}