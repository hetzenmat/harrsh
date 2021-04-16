package at.forsyte.harrsh.GSL.query

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.GSL.SID.{SID, SID_btw}
import at.forsyte.harrsh.GSL.{AliasingConstraint, GslFormula, Substitution, TypeComputation, query}
import at.forsyte.harrsh.seplog.{NullConst, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a satisfiability query which consists of a GSL formula and a corresponding SID
  */
case class Query(formula: GslFormula, sid: SID, fromEntailment: Boolean = false, status: Option[Boolean] = None) {

  private def decideSat(sidBTW: SID_btw): Boolean = {
    require(formula.predicateCalls subsetOf sidBTW.predicates.keySet, "All used predicates have to be defined")

    // Rename variables in formula s.t. free variables in the formula and free variables in the SID are disjoint
    val fvarsFormula = formula.freeVars
    val fvarsSID = sidBTW.freeVars

    val common = fvarsFormula intersect fvarsSID

    val fresh = Var.freshFreeVars(fvarsFormula union fvarsSID, common.size)

    val formulaRenamed = formula.substitute(Substitution.from(common.zip(fresh)))

    val newFvars = formulaRenamed.freeVars

    AliasingConstraint.allAliasingConstraints(newFvars.incl(NullConst)).exists(ac => {
      println("Current AC: " + ac + "\n")

      val tc = new TypeComputation(sidBTW, formulaRenamed)

      val types = tc.types(ac)

      println("Result: " + types)

      types.nonEmpty
    })
  }

  def isSatisfiable: Either[String, Boolean] = sid.toBtw.map(decideSat)

  def entailmentHolds: Either[String, Boolean] = {
    formula match {
      case _: Negation => isSatisfiable.map(!_)
      case _ => Left("This method can only be called on negations")
    }
  }
}

object Query {
  def fromEntailment(left: GslFormula, right: GslFormula, sid: SID): Query = query.Query(Negation(left, right), sid, fromEntailment = true)
}