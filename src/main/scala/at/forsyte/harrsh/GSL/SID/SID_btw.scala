package at.forsyte.harrsh.GSL.SID

import at.forsyte.harrsh.GSL.{RuleInstance, SymbolicHeapBtw, Utils}
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}

final class SID_btw(val predicates: Map[String, SID.Predicate[SymbolicHeapBtw]]) {

  val freeVars: Set[Var] = predicates.values.flatMap(_.freeVars).toSet

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
