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

    final case class Emp() extends GslFormula

    final case class Equality(left: Var, right: Var) extends GslFormula

    final case class DisEquality(left: Var, right: Var) extends GslFormula

    final case class PointsTo(from: Var, to: Seq[Var]) extends GslFormula

    final case class PredicateCall(pred: String, args: Seq[Var]) extends GslFormula

  }

  final case class SeparatingConjunction(left: GslFormula, right: GslFormula) extends GslFormula

  final case class StandardConjunction(left: GslFormula, right: GslFormula) extends GslFormula

  final case class Disjunction(left: GslFormula, right: GslFormula) extends GslFormula

  final case class Negation(guard: GslFormula, negated: GslFormula) extends GslFormula

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula

}