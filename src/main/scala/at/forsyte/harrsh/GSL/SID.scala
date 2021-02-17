package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.SID.{Predicate, establishedResultSuccess}
import at.forsyte.harrsh.heapautomata.instances.TrackingAutomata
import at.forsyte.harrsh.refinement.RefinementAlgorithms
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}
import at.forsyte.harrsh.seplog.inductive.{PointsTo, PredCall, RichSid, SepLogAtom, SidFactory, SymbolicHeap => SH}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent an SID
  */
case class SID(predicates: Map[String, SID.Predicate[SymbolicHeap]]) {
  def satisfiesProgress(pred: String): Boolean =
    predicates.contains(pred) && predicates(pred).predrootIndex >= 0

  lazy val satisfiesProgress: Boolean =
    predicates.keys.forall(p => satisfiesProgress(p))

  def satisfiesConnectivity(pred: String): Boolean =
    predicates.contains(pred) && predicates(pred).rules.forall(body => {
      body.calls.forall({ case Atom.PredicateCall(name, args) => predicates.contains(name) && body.lref.contains(args(predicates(name).predrootIndex)) })
    })

  lazy val satisfiesConnectivity: Boolean =
    predicates.keys.forall(p => satisfiesConnectivity(p))

  lazy val satisfiesEstablishment: Boolean = {
    predicates.keys.forall(p => {
      val sid = toRootedSid(p)
      println(sid)

      // Runs of establishment automaton and non-establishment automaton is somehow needed to also filter out
      // partially-established SIDs
      RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.establishmentAutomaton) == establishedResultSuccess &&
        RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.nonEstablishmentAutomaton) != establishedResultSuccess
    })
  }

  def toPointerClosedSID: Either[String, PointerClosedSID] = {
    if (satisfiesProgress) {
      if (satisfiesConnectivity) {
        if (satisfiesEstablishment) {
          Right(PointerClosedSID(predicates.map({
            case (name, Predicate(predName, args, bodies)) =>
              (name, Predicate(predName, args, bodies.map(_.toPointerClosedSymbolicHeap)))
          })))
        }
        else
          Left("SID does not satisfy establishment")
      } else
        Left("SID does not satisfy connectivity")
    } else
      Left("SID does not satisfy progress")
  }

  def allRuleInstancesForPointsTo(from: Int, to: Seq[Int], range: Range): Iterable[(Map[Var, Int], RuleInstance)] = {

    val candidates = for (pred <- predicates.values;
                          rule <- pred.rules;
                          instantiationSize = pred.args.length + rule.quantifiedVars.length;
                          instantiation <- Utils.allSeqsWithRange(instantiationSize, range);
                          subst: Map[Var, Int] = (rule.freeVars ++ (1 to rule.quantifiedVars.length).map(BoundVar)).zip(instantiation).toMap) yield (subst, rule.instantiate(pred, instantiation.take(pred.args.length), subst))

    candidates.collect({ case (v, Some(r@RuleInstance(_, _, from_, to_, _))) if from == from_ && to == to_ => (v, r) })
  }


  private def toRootedSid(startPred: String): RichSid = {
    val ruleTuples = predicates.flatMap({
      case (predName, pred) =>
        pred.rules.map(body => {
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
    }).toSeq

    SidFactory.makeRootedSid(startPred,
      "",
      predicates.map({
        case (predName, pred) => (predName, FreeVar(pred.args(pred.predrootIndex)))
      }),
      ruleTuples: _*)
  }
}

case class PointerClosedSID(predicates: Map[String, SID.Predicate[PointerClosedSymbolicHeap]]) {
}

object SID {

  private val establishedResultSuccess: Boolean = false

  case class Predicate[T <: AbstractSymbolicHeap](name: String, args: Seq[String], rules: Seq[T]) {

    /**
      * If the predicate satisfies progress, predrootIndex >= 0 and -1 otherwise.
      */
    val predrootIndex: Int = {
      args.indices.find(
        i => rules.forall(h => h match {
          case sh: SymbolicHeap => sh.spatial.size == 1 && sh.spatial.head.from == FreeVar(args(i))
          case sh: PointerClosedSymbolicHeap => val ptr = sh.calls.filter(_.pointsTo)
            if (ptr.size != 1) false
            else ptr.head.args.head == FreeVar(args(i))
        })
      ) match {
        case None => -1
        case Some(i) => i
      }
    }

    def predroot: FreeVar =
      FreeVar(args(predrootIndex))
  }

  case class Rule(name: String, args: Seq[String], body: SymbolicHeap) {
    if (args.toSet.size != args.size)
      throw RuleException("Repeated arguments")

    if (!body.freeVars.map(_.toString).subsetOf(args.toSet))
      throw RuleException("Free variables are not subset of rule arguments")

    if ("^ptr[1-9][0-9]+$".r.matches(name))
      throw RuleException("Reserved name ptr_k was used")
  }

  def apply(rules: Seq[Rule]): SID =
    SID(rules.foldLeft(Map.empty[String, Predicate[SymbolicHeap]]) {
      (map, rule) =>
        map.updatedWith(rule.name) {
          case None => Some(Predicate(rule.name, rule.args, Seq(rule.body)))
          case Some(pred) =>
            if (rule.args != pred.args)
              throw RuleException("Arguments have to be the same for all rules of a predicate")

            Some(Predicate(rule.name, rule.args, pred.rules.appended(rule.body)))
        }
    })
}

final case class RuleException(private val message: String = "",
                               private val cause: Throwable = None.orNull)
  extends Exception(message, cause)
