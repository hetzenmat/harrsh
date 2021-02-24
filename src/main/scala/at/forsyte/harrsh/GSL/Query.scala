package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.Var

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a satisfiability query which consists of a GSL formula and a corresponding SID
  */
case class Query(formula: GslFormula, sid: SID, fromEntailment: Boolean) {
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

        Right(AliasingConstraint.allAliasingConstraints(newFvars).exists(ac => {
          val tc = new TypeComputation(sidBTW, newFvars)

          tc.types(formulaRenamed, ac).nonEmpty
        }))
    }
}
