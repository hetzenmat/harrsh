package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
sealed trait GslFormula {
  type T <: GslFormula

  final def substitute(substitution: Map[Var, Var]): T = {

    val subst = substitution.toSeq.filter(t => t._1 != t._2 && t._1 != NullConst).toMap

    _substitute(subst)
  }

  def _substitute(substitution: Map[Var, Var]): T

  val varSeq: Seq[Var]
  final lazy val vars: Set[Var] = varSeq.toSet
  val predicateCalls: Set[String]
  lazy val freeVars: Set[Var] = vars.collect { case v: FreeVar => v }
}

object GslFormula {

  sealed trait Atom extends GslFormula {
    //type T = Atom
  }

  object Atom {

    final case class Emp() extends Atom {
      override type T = Emp

      override def _substitute(substitution: Map[Var, Var]): Emp = this

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq.empty
    }

    final case class Equality(left: Var, right: Var) extends Atom {
      override type T = Equality

      override def _substitute(substitution: Map[Var, Var]): Equality = Equality(substitution.getOrElse(left, left),
                                                                                substitution.getOrElse(right, right))

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq(left, right)
    }

    final case class DisEquality(left: Var, right: Var) extends Atom {
      override type T = DisEquality

      override def _substitute(substitution: Map[Var, Var]): DisEquality = DisEquality(substitution.getOrElse(left, left),
                                                                                      substitution.getOrElse(right, right))

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq(left, right)

      def toEquality: Equality = Equality(left, right)
    }

    final case class PointsTo(from: Var, to: Seq[Var]) extends Atom {
      override type T = PointsTo

      override def _substitute(substitution: Map[Var, Var]): PointsTo = PointsTo(substitution.getOrElse(from, from), to.map(v => substitution.getOrElse(v, v)))

      def ptrmodel(ac: AliasingConstraint[Var]): Map[Var, Int] =
        vars.foldLeft(Map(NullConst.asInstanceOf[Var] -> 0)) { (map, v) =>
          if (ac.domain.contains(v)) {
            if (ac =:= (v, NullConst))
              map.updated(v, 0)
            else
              map.updated(v, ac.eqClass(v) + 1)
          } else {
            map
          }
        }
//        vars
//          .diff(ac.domain)
//          .foldLeft((ac.eqClass.map(kv => (kv._1, if (ac =:= (kv._1, NullConst)) 0 else kv._2 + 1)), ac.domain.size + 2)) {
//            case ((map, ix), variable) => (map.updated(variable, ix), ix + 1)
//          }._1

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = from +: to
    }

    final case class PredicateCall(pred: String, args: Seq[Var]) extends Atom with Ordered[PredicateCall] {
      override type T = PredicateCall

      override def _substitute(substitution: Map[Var, Var]): PredicateCall = PredicateCall(pred, args.map(v => substitution.getOrElse(v, v)))

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
      override val varSeq: Seq[Var] = args
    }

  }

  final case class SeparatingConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = SeparatingConjunction

    override def _substitute(substitution: Map[Var, Var]): T =
      SeparatingConjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq

  }

  object SeparatingConjunction {
    def from(left: GslFormula, right: Seq[GslFormula]): SeparatingConjunction = right match {
      case head +: Seq() => SeparatingConjunction(left, head)
      case head +: tail => SeparatingConjunction(left, SeparatingConjunction.from(head, tail))
    }
  }

  final case class StandardConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = StandardConjunction

    override def _substitute(substitution: Map[Var, Var]): T =
      StandardConjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq
  }

  final case class Disjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Disjunction

    override def _substitute(substitution: Map[Var, Var]): T =
      Disjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq
  }

  final case class Negation(guard: GslFormula, negated: GslFormula) extends GslFormula {
    type T = Negation

    override def _substitute(substitution: Map[Var, Var]): T =
      Negation(guard.substitute(substitution), negated.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union negated.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ negated.varSeq
  }

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = MagicWand

    override def _substitute(substitution: Map[Var, Var]): T =
      MagicWand(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ left.varSeq ++ right.varSeq
  }

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    type T = Septraction

    override def _substitute(substitution: Map[Var, Var]): T =
      Septraction(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ left.varSeq ++ right.varSeq
  }

}