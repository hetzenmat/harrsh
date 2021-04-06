package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.SID.{Predicate, establishedResultSuccess}
import at.forsyte.harrsh.heapautomata.instances.TrackingAutomata
import at.forsyte.harrsh.refinement.RefinementAlgorithms
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}
import at.forsyte.harrsh.seplog.inductive.{PointsTo, PredCall, RichSid, SepLogAtom, SidFactory, SymbolicHeap => SH}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent an SID
  */
class SID private(val predicates: Map[String, SID.Predicate[SymbolicHeap]]) {
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

      // Runs of establishment automaton and non-establishment automaton is somehow needed to also filter out
      // partially-established SIDs
      RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.establishmentAutomaton) == establishedResultSuccess &&
        RefinementAlgorithms.onTheFlyRefinementWithEmptinessCheck(sid, TrackingAutomata.nonEstablishmentAutomaton) != establishedResultSuccess
    })
  }

  def toBtw: Either[String, SID_btw] = {
    if (satisfiesProgress) {
      if (satisfiesConnectivity) {
        if (satisfiesEstablishment) {
          val predicatesTransformed = predicates.map({
            case (name, Predicate(predName, args, rules)) =>
              (name, Predicate(predName, args, rules.map(_.toBtw)))
          })


          val pointsToSizes: Set[Int] = predicatesTransformed.values.flatMap(_.rules).map(_.pointsTo.to.size).toSet

          val predicatesWithPtrs = pointsToSizes.foldLeft(predicatesTransformed) { (map, number) =>
            val name = "ptr" + number
            val args = (1 to number + 1).map("x" + _)
            val argsV = args.map(FreeVar)
            map.updated(name, Predicate(name = name,
                                        args = args,
                                        rules = Seq(SymbolicHeapBtw(pointsTo = Atom.PointsTo(argsV.head, argsV.tail)))))
          }

          Right(new SID_btw(predicatesWithPtrs))
        }
        else
          Left("SID does not satisfy establishment")
      } else
        Left("SID does not satisfy connectivity")
    } else
      Left("SID does not satisfy progress")
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


class SID_btw(val predicates: Map[String, SID.Predicate[SymbolicHeapBtw]]) {

  val freeVars: Set[Var] = predicates.values.flatMap(_.freeVars).toSet

  val varBiMap: BiMap[Var, Int] = BiMap.from((NullConst, 0) +: freeVars.excl(NullConst).toSeq.sorted.zipWithIndex.map(t => (t._1, t._2 + 1)))
  val predBiMap: BiMap[String, Int] = BiMap.from(predicates.keys.toSeq.sorted.zipWithIndex.map(t => (t._1, t._2 + 1)))

  def allRuleInstancesForPointsTo(from: Int, to: Seq[Int], range: Range): Iterable[(Map[Var, Int], RuleInstance)] = {

    val candidates = for (pred <- predicates.values;
                          rule <- pred.rules if rule.pointsTo.to.length == to.length;
                          instantiationSize = pred.args.length + rule.quantifiedVars.length;
                          instantiation <- Utils.allSeqsWithRange(instantiationSize, range);
                          subst: Map[Var, Int] = (pred.args.map(FreeVar) ++ (1 to rule.quantifiedVars.length).map(BoundVar.apply)).zip(instantiation).toMap) yield (subst, rule.instantiate(pred, instantiation.take(pred.args.length), subst))

    candidates.collect({ case (v, Some(r@RuleInstance(_, _, from_, to_, _))) if from == from_ && to == to_ => (v, r) })
  }

  override def hashCode(): Int = predicates.hashCode()

  override def equals(obj: Any): Boolean = obj match {
    case value: SID_btw => predicates == value.predicates
    case _ => false
  }
}

object SID {

  private val establishedResultSuccess: Boolean = false

  case class Predicate[T <: AbstractSymbolicHeap](name: String, args: Seq[String], rules: Seq[T]) {

    val freeVars: Set[Var] = args.map(FreeVar).toSet

    /**
      * If the predicate satisfies progress, predrootIndex >= 0 and -1 otherwise.
      */
    val predrootIndex: Int = {
      args.indices.find(
        i => rules.forall {
          case sh: SymbolicHeap => sh.spatial.size == 1 && sh.spatial.head.from == FreeVar(args(i))
          case sh: SymbolicHeapBtw => sh.pointsTo.from == FreeVar(args(i))
        }
        ) match {
        case None => -1
        case Some(i) => i
      }
    }

    def predroot: FreeVar =
      FreeVar(args(predrootIndex))

  }

  case class Rule(name: String, args: Seq[String], body: SymbolicHeap) {
    require(args.toSet.size == args.size, "Repeated arguments")

    require(body.freeVars.map(_.toString) == args.toSet, "Free variables need to be arguments")

    require(!"^ptr[1-9][0-9]+$".r.matches(name), "Reserved name ptr was used")
  }

  def buildSID(rules: Seq[Rule]): SID =
    new SID(rules.foldLeft(Map.empty[String, Predicate[SymbolicHeap]]) {
      (map, rule) =>
        map.updatedWith(rule.name) {
          case None => Some(Predicate(rule.name, rule.args, Seq(rule.body)))
          case Some(pred) =>
            require(rule.args == pred.args, "Arguments have to be the same for all rules of a predicate")

            Some(Predicate(rule.name, rule.args, pred.rules.appended(rule.body)))
        }
    })
}

final case class RuleException(private val message: String = "",
                               private val cause: Throwable = None.orNull)
  extends Exception(message, cause)
