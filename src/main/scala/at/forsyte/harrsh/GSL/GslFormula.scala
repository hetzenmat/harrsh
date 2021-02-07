package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.Var

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
sealed abstract class GslFormula

object GslFormula {

  sealed abstract class Atom

  object Atom {

    final case class Emp()

    final case class Equality(left: Var, right: Var)

    final case class DisEquality(left: Var, right: Var)

    final case class PointsTo(from: Var, toHead: Var, toRest: Seq[Var]) // to ensure that 'from' points to a non-empty sequence

    final case class PredicateCall(pred: String, args: Seq[Var])

  }

  final case class SeparatingConjunction(left: GslFormula, right: GslFormula)

  final case class StandardConjunction(left: GslFormula, right: GslFormula)

  final case class Disjunction(left: GslFormula, right: GslFormula)

  final case class Negation(guard: GslFormula, negated: GslFormula)

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula)

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula)

}