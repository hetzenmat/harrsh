package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.StackForestProjection.TreeProjection
import at.forsyte.harrsh.seplog.{BoundVar, Var}


/**
  * Created by Matthias Hetzenberger on 2021-02-12
  *
  * A stack-forest projection
  */
case class StackForestProjection(guardedExistentials: Seq[BoundVar], guardedUniversals: Seq[BoundVar], formula: Seq[TreeProjection]) {
  private val existentialSet = guardedExistentials.toSet
  private val universalSet = guardedUniversals.toSet

  val quantifiedLength: Int = guardedExistentials.size + guardedUniversals.size

  if ((existentialSet.size != guardedExistentials.size) ||
    (universalSet.size != guardedUniversals.size))
    throw new IllegalArgumentException("No duplicates allowed in quantified variables")

  if (existentialSet.intersect(universalSet).nonEmpty)
    throw new IllegalArgumentException("No duplicates between quantifier blocks allowed")

  def replaceQuantifiedVariables(replacements: Seq[BoundVar]): Seq[TreeProjection] = {
    if (quantifiedLength != replacements.size)
      throw new IllegalArgumentException("Size of quantified variables does not match")

    val subst: Map[Var, Var] = (guardedExistentials ++ guardedUniversals).zip(replacements).toMap
    formula.map({ case (calls, call) => (calls.map(_.substitute(subst)), call.substitute(subst)) })
  }

  override def toString: String = {
    (if (guardedExistentials.nonEmpty) guardedExistentials.mkString("∃ ", " ", ". ") else "") +
      (if (guardedUniversals.nonEmpty) guardedUniversals.mkString("∀ ", " ", ". ") else "") + formula.map({ case (calls, call) =>
      if (calls.isEmpty)
        call.toString
      else if (calls.size == 1)
        "(" + calls.head + " -* " + call + ")"
      else
        "((" + calls.mkString(" * ") + ") -* " + call + ")"
    }).mkString(" * ")
  }
}

object StackForestProjection {
  type TreeProjection = (Seq[GslFormula.Atom.PredicateCall], GslFormula.Atom.PredicateCall)

  def boundVariables(formula: Seq[TreeProjection]): Set[BoundVar] = {
    formula.flatMap({ case (calls, call) =>
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
        Some(StackForestProjection(d1 ++ d2, a.toSet.intersect(StackForestProjection.boundVariables(formula)).toSeq, formula))
      } else None
    }).flatten.toSet
  }
}