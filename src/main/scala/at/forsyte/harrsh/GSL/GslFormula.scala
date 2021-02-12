package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{BoundVar, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
sealed abstract class GslFormula {
  type T <: GslFormula

  def substitute(substitution: Map[Var, Var]): T
}

object GslFormula {

  sealed abstract class Atom extends GslFormula {
    type T = Atom

    def vars: Set[Var]
  }

  object Atom {

    final case class Emp() extends Atom {
      override def substitute(substitution: Map[Var, Var]): Emp = this

      override def vars: Set[Var] = Set.empty
    }

    final case class Equality(vars: Set[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): Equality = new Equality(vars.map(v => substitution.getOrElse(v, v)))
    }

    object Equality {
      def apply(left: Var, right: Var): Equality = Equality(Set(left, right))
    }

    final case class DisEquality(vars: Set[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): DisEquality = new DisEquality(vars.map(v => substitution.getOrElse(v, v)))
    }

    object DisEquality {
      def apply(left: Var, right: Var): DisEquality = DisEquality(Set(left, right))
    }

    final case class PointsTo(from: Var, to: Seq[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): PointsTo = PointsTo(substitution.getOrElse(from, from), to.map(v => substitution.getOrElse(v, v)))

      override def vars: Set[Var] = to.prepended(from).toSet
    }

    final case class PredicateCall(pred: String, args: Seq[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): PredicateCall = PredicateCall(pred, args.map(v => substitution.getOrElse(v, v)))

      override def vars: Set[Var] = args.toSet

      def boundVars: Set[BoundVar] = args.collect({ case v: BoundVar => v }).toSet

      def pointsTo: Boolean = "^ptr[1-9][0-9]+$".r.matches(pred)

      override def toString: String = {
        pred + args.mkString("(", ", ", ")")
      }
    }

  }

  final case class SeparatingConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = SeparatingConjunction

    override def substitute(substitution: Map[Var, Var]): T =
      SeparatingConjunction(left.substitute(substitution), right.substitute(substitution))
  }

  final case class StandardConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = StandardConjunction

    override def substitute(substitution: Map[Var, Var]): T =
      StandardConjunction(left.substitute(substitution), right.substitute(substitution))
  }

  final case class Disjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Disjunction

    override def substitute(substitution: Map[Var, Var]): T =
      Disjunction(left.substitute(substitution), right.substitute(substitution))
  }

  final case class Negation(guard: GslFormula, negated: GslFormula) extends GslFormula {
    type T = Negation

    override def substitute(substitution: Map[Var, Var]): T =
      Negation(guard.substitute(substitution), negated.substitute(substitution))
  }

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = MagicWand

    override def substitute(substitution: Map[Var, Var]): T =
      MagicWand(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))
  }

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Septraction

    override def substitute(substitution: Map[Var, Var]): T =
      Septraction(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))
  }

}