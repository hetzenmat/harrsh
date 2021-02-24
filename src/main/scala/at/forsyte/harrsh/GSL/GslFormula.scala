package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
sealed trait GslFormula {
  type T <: GslFormula

  def substitute(substitution: Map[Var, Var]): T
}

object GslFormula {

  sealed trait Atom extends GslFormula {
    type T = Atom

    def vars: Set[Var]
  }

  object Atom {

    final case class Emp() extends Atom {
      override def substitute(substitution: Map[Var, Var]): Emp = this

      override def vars: Set[Var] = Set.empty
    }

    final case class Equality(left: Var, right: Var) extends Atom {

      override def substitute(substitution: Map[Var, Var]): Equality = Equality(substitution.getOrElse(left, left),
                                                                                substitution.getOrElse(right, right))

      override def vars: Set[Var] = Set(left, right)
    }

    final case class DisEquality(left: Var, right: Var) extends Atom {
      override def substitute(substitution: Map[Var, Var]): DisEquality = DisEquality(substitution.getOrElse(left, left),
                                                                                      substitution.getOrElse(right, right))


      override def vars: Set[Var] = Set(left, right)
    }

    final case class PointsTo(from: Var, to: Seq[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): PointsTo = PointsTo(substitution.getOrElse(from, from), to.map(v => substitution.getOrElse(v, v)))

      def ptrmodel(ac: AliasingConstraint): Map[Var, Int] = ac.eqClass.map(kv => (kv._1, kv._2 + 1))

      override def vars: Set[Var] = to.prepended(from).toSet
    }

    final case class PredicateCall(pred: String, args: Seq[Var]) extends Atom with Ordered[PredicateCall] {
      override def substitute(substitution: Map[Var, Var]): PredicateCall = PredicateCall(pred, args.map(v => substitution.getOrElse(v, v)))

      override def vars: Set[Var] = args.toSet

      def boundVars: Set[BoundVar] = args.collect({ case v: BoundVar => v }).toSet

      def freeVars: Set[FreeVar] = args.collect({ case v: FreeVar => v }).toSet

      def pointsTo: Boolean = "^ptr[1-9][0-9]+$".r.matches(pred)

      override def toString: String = {
        pred + args.mkString("(", ", ", ")")
      }

      override def compare(that: PredicateCall): Int = {
        val res = pred.compare(that.pred)
        if (res == 0)
          Utils.compareLexicographically(args, that.args)
        else
          res
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