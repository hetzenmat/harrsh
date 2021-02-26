package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
sealed trait GslFormula {
  type T <: GslFormula

  def substitute(substitution: Map[Var, Var]): T

  val vars: Set[Var]
  val predicateCalls: Set[String]
  lazy val freeVars: Set[Var] = vars.collect { case v: FreeVar => v }
}

object GslFormula {

  sealed trait Atom extends GslFormula {
    type T = Atom
  }

  object Atom {

    final case class Emp() extends Atom {
      override def substitute(substitution: Map[Var, Var]): Emp = this

      override val vars: Set[Var] = Set.empty
      override val predicateCalls: Set[String] = Set.empty
    }

    final case class Equality(left: Var, right: Var) extends Atom {

      override def substitute(substitution: Map[Var, Var]): Equality = Equality(substitution.getOrElse(left, left),
                                                                                substitution.getOrElse(right, right))

      override val vars: Set[Var] = Set(left, right)
      override val predicateCalls: Set[String] = Set.empty
    }

    final case class DisEquality(left: Var, right: Var) extends Atom {
      override def substitute(substitution: Map[Var, Var]): DisEquality = DisEquality(substitution.getOrElse(left, left),
                                                                                      substitution.getOrElse(right, right))


      override val vars: Set[Var] = Set(left, right)
      override val predicateCalls: Set[String] = Set.empty
    }

    final case class PointsTo(from: Var, to: Seq[Var]) extends Atom {
      override def substitute(substitution: Map[Var, Var]): PointsTo = PointsTo(substitution.getOrElse(from, from), to.map(v => substitution.getOrElse(v, v)))

      def ptrmodel(ac: AliasingConstraint): Map[Var, Int] = vars.diff(ac.domain).foldLeft((ac.eqClass.map(kv => (kv._1, kv._2 + 1)).updated(NullConst, 0), ac.domain.size + 2)) {
        case ((map, ix), variable) => (map.updated(variable, ix), ix + 1)
      }._1

      override val vars: Set[Var] = (to :+ from).toSet.excl(NullConst)
      override val predicateCalls: Set[String] = Set.empty

    }

    final case class PredicateCall(pred: String, args: Seq[Var]) extends Atom with Ordered[PredicateCall] {
      override def substitute(substitution: Map[Var, Var]): PredicateCall = PredicateCall(pred, args.map(v => substitution.getOrElse(v, v)))

      override val vars: Set[Var] = args.toSet

      def boundVars: Set[BoundVar] = args.collect({ case v: BoundVar => v }).toSet

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

      override val predicateCalls: Set[String] = Set(pred)
    }

  }

  final case class SeparatingConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = SeparatingConjunction

    override def substitute(substitution: Map[Var, Var]): T =
      SeparatingConjunction(left.substitute(substitution), right.substitute(substitution))

    override val vars: Set[Var] = left.vars union right.vars
    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
  }

  object SeparatingConjunction {
    def from(left: GslFormula, right: Seq[GslFormula]): SeparatingConjunction = right match {
      case head +: Seq() => SeparatingConjunction(left, head)
      case head +: tail => SeparatingConjunction(left, SeparatingConjunction.from(head, tail))
    }
  }

  final case class StandardConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = StandardConjunction

    override def substitute(substitution: Map[Var, Var]): T =
      StandardConjunction(left.substitute(substitution), right.substitute(substitution))

    override val vars: Set[Var] = left.vars union right.vars
    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
  }

  final case class Disjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Disjunction

    override def substitute(substitution: Map[Var, Var]): T =
      Disjunction(left.substitute(substitution), right.substitute(substitution))

    override val vars: Set[Var] = left.vars union right.vars
    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
  }

  final case class Negation(guard: GslFormula, negated: GslFormula) extends GslFormula {
    type T = Negation

    override def substitute(substitution: Map[Var, Var]): T =
      Negation(guard.substitute(substitution), negated.substitute(substitution))

    override val vars: Set[Var] = guard.vars union negated.vars
    override val predicateCalls: Set[String] = guard.predicateCalls union negated.predicateCalls
  }

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = MagicWand

    override def substitute(substitution: Map[Var, Var]): T =
      MagicWand(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val vars: Set[Var] = guard.vars union left.vars union right.vars
    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls

  }

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Septraction

    override def substitute(substitution: Map[Var, Var]): T =
      Septraction(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val vars: Set[Var] = guard.vars union left.vars union right.vars
    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls
  }

}