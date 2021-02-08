package at.forsyte.harrsh.GSL

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a satisfiability query which consists of a GSL formula and a corresponding SID
  */
case class Query(formula: GslFormula, sid: SID) {
}
