package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.StackForestProjection.boundVariables
import at.forsyte.harrsh.seplog.{BoundVar, Var}

import scala.collection.SortedSet

/**
  * Created by Matthias Hetzenberger on 2021-02-12
  *
  * A stack-forest projection
  */
class StackForestProjection(val guardedExistentials: SortedSet[BoundVar], val guardedUniversals: SortedSet[BoundVar], val formula: Seq[TreeProjection]) {

  val quantifiedLength: Int = guardedExistentials.size + guardedUniversals.size

  if (guardedExistentials.intersect(guardedUniversals).nonEmpty)
    throw new IllegalArgumentException("No duplicates between quantifier blocks allowed")

  if (boundVariables(formula) != guardedExistentials.union(guardedUniversals)) {

    println(boundVariables(formula))
    throw new IllegalArgumentException("Set of bound variables is not equal to set of quantified variables")
  }

  if (!Utils.isSorted(formula)) {
    println(this)
    throw new IllegalArgumentException("Tree projections have to be sorted")
  }

  def replaceQuantifiedVariables(replacements: Seq[BoundVar]): Seq[TreeProjection] = {
    if (guardedExistentials.size + guardedUniversals.size != replacements.size)
      throw new IllegalArgumentException("Size of quantified variables does not match")

    val replEx = replacements.take(guardedExistentials.size)
    val replUn = replacements.drop(guardedExistentials.size)

    val subst: Map[Var, Var] = (guardedExistentials.zip(replEx) ++ guardedUniversals.zip(replUn)).toMap
    formula.map({ case TreeProjection(calls, call) => TreeProjection(calls.map(_.substitute(subst)), call.substitute(subst)) }).sorted
  }

  override def toString: String = {
    (if (guardedExistentials.nonEmpty) guardedExistentials.mkString("∃ ", " ", ". ") else "") +
      (if (guardedUniversals.nonEmpty) guardedUniversals.mkString("∀ ", " ", ". ") else "") + formula.map({ case TreeProjection(calls, call) =>
      if (calls.isEmpty)
        call.toString
      else if (calls.size == 1)
        "(" + calls.head + " -* " + call + ")"
      else
        "((" + calls.mkString(" * ") + ") -* " + call + ")"
    }).mkString(" * ")
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case v: StackForestProjection => v.guardedExistentials == guardedExistentials && v.guardedUniversals == guardedUniversals && Utils.compareLexicographically(formula, v.formula) == 0
      case _ => false
    }
  }
}

object StackForestProjection {

  def from(guardedExistentials: SortedSet[BoundVar],
           guardedUniversals: SortedSet[BoundVar],
           formula: Seq[TreeProjection]): StackForestProjection = new StackForestProjection(guardedExistentials, guardedUniversals, formula.sorted)

  def boundVariables(formula: Seq[TreeProjection]): Set[BoundVar] = {
    formula.flatMap({ case TreeProjection(calls, call) =>
      calls.flatMap(_.boundVars) ++ call.boundVars
    }).toSet
  }

  def allRescopings(left: StackForestProjection, right: StackForestProjection): Set[StackForestProjection] = {
    (for (i <- 0 to left.quantifiedLength;
          j <- 0 to right.quantifiedLength) yield {
      val d1 = (1 to i).map(i => BoundVar(i))
      val d2 = (1 to j).map(i => BoundVar(i + d1.length))
      val a = (1 to Math.max(left.quantifiedLength - d1.length, right.quantifiedLength - d2.length)).map(i => BoundVar(i + d1.length + d2.length))

      val u1size = left.quantifiedLength - d1.length
      val u2size = right.quantifiedLength - d2.length

      val u1 = (d2 ++ a).take(u1size)
      val u2 = (d1 ++ a).take(u2size)

      val disjoints = a ++ d1 ++ d2
      if (disjoints.size == disjoints.toSet.size &&
        u1.toSet.subsetOf(a.toSet.union(d2.toSet)) &&
        u2.toSet.subsetOf(a.toSet.union(d1.toSet))) {
        val formula = left.replaceQuantifiedVariables(d1 ++ u1) ++ right.replaceQuantifiedVariables(d2 ++ u2)
        Some(StackForestProjection.from(SortedSet.from(d1 ++ d2), SortedSet.from(a.toSet.intersect(StackForestProjection.boundVariables(formula))), formula))
      } else None
    }).flatten.toSet
  }
}

case class TreeProjection(allholepreds: Seq[GslFormula.Atom.PredicateCall], rootpred: GslFormula.Atom.PredicateCall) extends Ordered[TreeProjection] {
  if (!Utils.isSorted(allholepreds))
    throw new IllegalArgumentException("allholepreds have to be sorted")

  override def compare(that: TreeProjection): Int = {
    val res = Utils.compareLexicographically(allholepreds, that.allholepreds)
    if (res == 0)
      rootpred.compare(that.rootpred)
    else
      res
  }
}