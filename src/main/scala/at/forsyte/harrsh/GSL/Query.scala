package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.seplog.{NullConst, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a satisfiability query which consists of a GSL formula and a corresponding SID
  */
case class Query(formula: GslFormula, sid: SID, fromEntailment: Boolean = false, status: Option[Boolean] = None) {

  def isSatisfiable: Either[String, Boolean] =
    sid.toBtw match {
      case Left(l) => Left(l)
      case Right(sidBTW) =>

        require(formula.predicateCalls subsetOf sidBTW.predicates.keySet, "All used predicates have to be defined")

        // Rename variables in formula s.t. free variables in the formula and free variables in the SID are disjoint
        val fvarsFormula = formula.freeVars
        val fvarsSID = sidBTW.freeVars

        val common = fvarsFormula intersect fvarsSID

        val fresh = Var.freshFreeVars(fvarsFormula union fvarsSID, common.size)

        val subst = common.zip(fresh).toMap

        val formulaRenamed = formula.substitute(subst)

        val newFvars = formulaRenamed.freeVars

        Right(AliasingConstraint.allAliasingConstraints(newFvars.incl(NullConst)).exists(ac => {
          println("Current AC: " + ac + "\n")

          val tc = new TypeComputation(sidBTW, formulaRenamed)

          val types = tc.types(ac)

          println("Result: " + types)

          types.nonEmpty
        }))
    }

  def entailmentHolds: Either[String, Boolean] = {
    formula match {
      case _: Negation => isSatisfiable match {
        case l@Left(_) => l
        case Right(result) => Right(!result)
      }
      case _ => Left("This method can only be called on negations")
    }
  }
}

object Query {
  def fromEntailment(left: GslFormula, right: GslFormula, sid: SID): Query = Query(Negation(left, right), sid, fromEntailment = true)
}