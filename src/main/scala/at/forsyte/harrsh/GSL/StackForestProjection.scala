package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.StackForestProjection.boundVariables
import at.forsyte.harrsh.seplog.{BoundVar, Var}

import scala.collection.SortedSet
import scala.runtime.ScalaRunTime

/**
  * Created by Matthias Hetzenberger on 2021-02-12
  *
  * A stack-forest projection
  */
class StackForestProjection(val guardedExistentials: SortedSet[BoundVar], val guardedUniversals: SortedSet[BoundVar], val formula: Seq[TreeProjection]) {

  val quantifiedLength: Int = guardedExistentials.size + guardedUniversals.size

  require(guardedExistentials.intersect(guardedUniversals).isEmpty,
          "No duplicates between quantifier blocks allowed")

  require(boundVariables(formula) == guardedExistentials.union(guardedUniversals),
          "Set of bound variables is not equal to set of quantified variables")

  require(Utils.isSorted(formula), "Tree projections have to be sorted")

  require(guardedExistentials.map(_.index) == SortedSet.from(1 to guardedExistentials.size) &&
            guardedUniversals.map(_.index) == SortedSet.from((1 to guardedUniversals.size).map(_ + guardedExistentials.size)),
          "Quantified variables must have consecutive indices starting with 1")

  def replaceQuantifiedVariables(replacements: Seq[BoundVar]): Seq[TreeProjection] = {
    if (guardedExistentials.size + guardedUniversals.size != replacements.size)
      throw new IllegalArgumentException("Size of quantified variables does not match")

    val replEx = replacements.take(guardedExistentials.size)
    val replUn = replacements.drop(guardedExistentials.size)

    val subst: Map[Var, Var] = (guardedExistentials.zip(replEx) ++ guardedUniversals.zip(replUn)).toMap
    formula.map({ case TreeProjection(calls, call) => TreeProjection(calls.map(_.substitute(subst)), call.substitute(subst)) }).sorted
  }

  def derivableSet: Set[StackForestProjection] = {
    oneStepDerivableSet ++ oneStepDerivableSet.flatMap(_.derivableSet)
  }

  /**
    * Compute the set of all one-step derivable projections wrt. to the generalized modus ponens rule (Definition 7.29)
    */
  def oneStepDerivableSet: Set[StackForestProjection] = {
    val formulaWithIndex = formula.zipWithIndex
    (for (projs <- formulaWithIndex;
          i = projs._2;
          f = projs._1) yield {
      formulaWithIndex.flatMap({
        case (TreeProjection(calls, rootpred), j) if i != j =>
          val ix = calls.indexOf(f.rootpred)
          if (ix == -1)
            None
          else {
            val newProj = TreeProjection((calls.zipWithIndex.collect({ case (v, k) if k != ix => v }) ++ f.allholepreds).sorted,
                                         rootpred)

            val newFormulas = formulaWithIndex.collect({ case (v, k) if k != i && k != j => v }) :+ newProj
            val boundVars = boundVariables(newFormulas)
            Some(StackForestProjection.from(guardedExistentials.intersect(boundVars),
                                            guardedUniversals.intersect(boundVars),
                                            newFormulas))
          }
        case _ => None
      }).toSet
    }).flatten.toSet
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

  override def hashCode(): Int = {
    ScalaRunTime._hashCode((guardedExistentials, guardedUniversals, formula)) // System.identityHashCode()
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

  def composition(left: StackForestProjection, right: StackForestProjection): Set[StackForestProjection] = {
    allRescopings(left, right).flatMap(sfp => sfp.derivableSet)
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