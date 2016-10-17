package slex.heapautomata

import slex.main.SlexLogging
import slex.seplog.SID

import scala.annotation.tailrec


/**
  * Created by jens on 10/15/16.
  */
object RefinementAlgorithms extends SlexLogging {

  def refineSID(sid : SID, ha : HeapAutomaton) : SID = {
    // TODO: Implement
    ???
  }

  /**
    * @return True iff there is no RSH in the refinement of sid by ha
    */
  def onTheFlyEmptinessCheck(sid : SID, ha : HeapAutomaton) : Boolean = {
    logger.debug("On the fly emptiness check for:")
    logger.debug("HA '" + ha.description + "' with states: " + ha.states)
    logger.debug("SID: " + sid)

    computeRefinementFixedPoint(sid, sid.startPred, ha)(Set())
  }

  @tailrec
  private def computeRefinementFixedPoint(sid : SID, pred : String, ha : HeapAutomaton)(r : Set[(String, ha.State)]) : Boolean = {

    // TODO: Also less efficient than possible due to naive data structure choice
    def reachedStatesForPred(rel : Set[(String, ha.State)], call : String) : Set[ha.State] = rel filter (_._1 == call) map (_._2)

    def allDefinedSources(rel : Set[(String, ha.State)], calls : Seq[String]) : Set[Seq[ha.State]] = {
      if (calls.length == 0) {
        Set(Seq())
      } else {
        for {
          tail <- allDefinedSources(rel, calls.tail)
          head <- reachedStatesForPred(rel, calls.head)
        } yield head +: tail
      }
    }

    // TODO: This would be more efficient if we used a more clever data structure for r
    val discoveredStartPredicate = r.find(p => p._1 == pred && ha.isFinal(p._2))
    if (discoveredStartPredicate.isDefined) {
      // There is a derivation that reaches a final state, refined language nonempty
      logger.debug("Reached " + discoveredStartPredicate.get + ", language non-empty")
      false
    } else {
      val newPairs : Set[(String, ha.State)] = for {
        trg <- ha.states
        (head, body) <- sid.rules
        src <- allDefinedSources(r, body.calledPreds)
        if (ha.isTransitionDefined(src, trg, body))
      } yield (head, trg)

      logger.debug("Discovered predicates: " + newPairs.mkString((", ")))

      val union = r union newPairs
      if (union.size == r.size) {
        // Fixed point reached without reaching a pred--final-state pair
        logger.debug("Reached fixed point, language is empty")
        true
      } else {
        // Fixed point not yet reached, recurse
        computeRefinementFixedPoint(sid, pred, ha)(union)
      }
    }
  }


}