package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.establishedResultSuccess
import at.forsyte.harrsh.heapautomata.instances.TrackingAutomata
import at.forsyte.harrsh.refinement.RefinementAlgorithms
import at.forsyte.harrsh.seplog.FreeVar
import at.forsyte.harrsh.seplog.inductive.{PointsTo, PredCall, RichSid, SepLogAtom, SidFactory, SymbolicHeap => SH}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent an SID
  */
case class SID(predicates: Map[String, SID.Predicate]) {
  def satisfiesProgress(pred: String): Boolean =
    predicates.contains(pred) && predicates(pred).predroot >= 0

  def satisfiesProgress: Boolean =
    predicates.keys.forall(satisfiesProgress)

  def satisfiesEstablishment: Boolean = {
    predicates.keys.forall(p => {
      val sid = toRootedSid(p)
      println(sid)

      // Runs of establishment automaton and non-establishment automaton is somehow needed to also filter out
      // partially-established SIDs
      RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.establishmentAutomaton) == establishedResultSuccess &&
        RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.nonEstablishmentAutomaton) != establishedResultSuccess
    })
  }

  private def toRootedSid(startPred: String): RichSid = {
    SidFactory.makeRootedSid(startPred,
      "",
      predicates.map({ case (predName, pred) => (predName, FreeVar(pred.args(pred.predroot))) }),
      predicates.flatMap({ case (predName, pred) =>
        pred.bodies.map(body => {
          val spatial: Seq[SepLogAtom] = body.spatial.map(p => PointsTo(p.from, p.to))
          val pure: Seq[SepLogAtom] = body.equalities.map(p =>
            if (p.vars.size == 1)
              p.vars.head =:= p.vars.head
            else
              p.vars.head =:= p.vars.tail.head
          ) ++
            body.disEqualities.map(p =>
              if (p.vars.size == 1)
                p.vars.head =/= p.vars.head
              else
                p.vars.head =/= p.vars.tail.head
            )
          val calls: Seq[SepLogAtom] = body.calls.map(p => PredCall(p.pred, p.args))
          (predName, body.quantifiedVars, SH(spatial ++ pure ++ calls: _*))
        })
      }).toSeq: _*
    )
  }
}

object SID {

  private val establishedResultSuccess: Boolean = false

  case class Predicate(name: String, args: Seq[String], bodies: Seq[SymbolicHeap]) {

    /**
      * If the predicate satisfies progress, predroot >= 0 and -1 otherwise.
      */
    def predroot: Int = {
      args.indices.find(
        i => bodies.forall(h => h.spatial.size == 1 && h.spatial.head.from == FreeVar(args(i)))
      ) match {
        case None => -1
        case Some(i) => i
      }
    }

  }

  case class Rule(name: String, args: Seq[String], body: SymbolicHeap) {
    if (args.toSet.size != args.size)
      throw RuleException("Repeated arguments")

    if (!body.freeVars.map(_.toString).subsetOf(args.toSet))
      throw RuleException("Free variables are not subset of rule arguments")

    if ("^ptr[0-9]+$".r.matches(name))
      throw RuleException("Reserved name ptr_k was used")
  }

  def apply(rules: Seq[Rule]): SID =
    SID(rules.foldLeft(Map.empty[String, Predicate]) {
      (map, rule) =>
        map.updatedWith(rule.name) {
          case None => Some(Predicate(rule.name, rule.args, Seq(rule.body)))
          case Some(pred) =>
            if (rule.args != pred.args)
              throw RuleException("Arguments have to be the same for all rules of a predicate")

            Some(Predicate(rule.name, rule.args, pred.bodies.appended(rule.body)))
        }
    })
}

final case class RuleException(private val message: String = "",
                               private val cause: Throwable = None.orNull)
  extends Exception(message, cause)
