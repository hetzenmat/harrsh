package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * ADT to model GSL formulae
  */
trait GslFormula {
  self =>
  type T <: GslFormula {type T = self.T}

  def substitute(substitution: Substitution[Var]): T = {
    _substitute(substitution.filterKeys(_ != NullConst))
  }

  def _substitute(substitution: Substitution[Var]): T

  val varSeq: Seq[Var]
  final lazy val vars: Set[Var] = varSeq.toSet
  val predicateCalls: Set[String]
  lazy val freeVars: Set[Var] = vars.collect { case v: FreeVar => v }
}

object GslFormula {

  abstract class Atom extends GslFormula

  object Atom {

    final case object Emp extends Atom {
      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq.empty

      override def _substitute(substitution: Substitution[Var]): this.type = this

      override def toString: String = "emp"

      override type T = this.type
    }

    final case class Equality(left: Var, right: Var) extends Atom {
      override type T = Equality

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq(left, right)

      override def _substitute(substitution: Substitution[Var]): Equality = Equality(substitution(left), substitution(right))

      override def toString: String = left + "= " + right
    }

    final case class DisEquality(left: Var, right: Var) extends Atom {
      override type T = DisEquality

      override def _substitute(substitution: Substitution[Var]): DisEquality = DisEquality(substitution(left), substitution(right))

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = Seq(left, right)

      def toEquality: Equality = Equality(left, right)

      override def toString: String = left + "!= " + right
    }

    //    final case class Equality(left: Var, right: Var) extends Atom {
    //      override type T = Equality
    //
    //      override def _substitute(substitution: Substitution[Var]): Equality = Equality(substitution(left), substitution(right))
    //
    //      override val predicateCalls: Set[String] = Set.empty
    //      override val varSeq: Seq[Var] = Seq(left, right)
    //    }
    //
    //    final case class DisEquality(left: Var, right: Var) extends Atom {
    //      override type T = DisEquality
    //
    //      override def _substitute(substitution: Map[Var, Var]): DisEquality = DisEquality(substitution.getOrElse(left, left),
    //                                                                                       substitution.getOrElse(right, right))
    //
    //      override val predicateCalls: Set[String] = Set.empty
    //      override val varSeq: Seq[Var] = Seq(left, right)
    //
    //      def toEquality: Equality = Equality(left, right)
    //    }

    final case class PointsTo(from: Var, to: Seq[Var]) extends Atom {
      require(to.nonEmpty)

      override type T = PointsTo

      override def _substitute(substitution: Substitution[Var]): PointsTo = PointsTo(substitution(from), to.map(substitution.apply))

      def ptrmodel(ac: AliasingConstraint[Var]): Map[Var, Int] =
        vars.foldLeft(Map(NullConst -> 0): Map[Var, Int]) { (map, v) =>
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

      override def toString: String = from + " -> " + (to match {
        case Seq(a) => a
        case _ => to.mkString("<", ", ", ">")
      })

      override val predicateCalls: Set[String] = Set.empty
      override val varSeq: Seq[Var] = from +: to
    }

    final case class PredicateCall(pred: String, args: Seq[Var]) extends Atom with Ordered[PredicateCall] {

      override type T = PredicateCall

      override def _substitute(substitution: Substitution[Var]): PredicateCall = PredicateCall(pred, args.map(substitution.apply))

      def boundVars: Set[BoundVar] = args.collect({ case v: BoundVar => v }).toSet

      def getRootArgument(sid: SID_btw): Var = args(sid.predicates(pred).predrootIndex)

      override def toString: String = pred + args.mkString("(", ", ", ")")

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
    override type T = SeparatingConjunction

    override def _substitute(substitution: Substitution[Var]): SeparatingConjunction =
      SeparatingConjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq

    override def toString: String = "(" + left + ") * (" + right + ")"
  }

  object SeparatingConjunction {
    def from(left: GslFormula, right: Seq[GslFormula]): SeparatingConjunction = right match {
      case head +: Seq() => SeparatingConjunction(left, head)
      case head +: tail => SeparatingConjunction(left, SeparatingConjunction.from(head, tail))
    }
  }

  final case class StandardConjunction(left: GslFormula, right: GslFormula) extends GslFormula {
    override type T = StandardConjunction

    override def _substitute(substitution: Substitution[Var]): StandardConjunction =
      StandardConjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq

    override def toString: String = "(" + left + ") /\\ (" + right + ")"
  }

  final case class Disjunction(left: GslFormula, right: GslFormula) extends GslFormula {

    override type T = Disjunction

    override def _substitute(substitution: Substitution[Var]): Disjunction =
      Disjunction(left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = left.varSeq ++ right.varSeq

    override def toString: String = "(" + left + ") \\/ (" + right + ")"
  }

  final case class Negation(guard: GslFormula, negated: GslFormula) extends GslFormula {

    override type T = Negation

    override def _substitute(substitution: Substitution[Var]): Negation =
      Negation(guard.substitute(substitution), negated.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union negated.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ negated.varSeq

    override def toString: String = "(" + guard + ") /\\ ~(" + negated + ")"
  }

  final case class MagicWand(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {

    override type T = MagicWand

    override def _substitute(substitution: Substitution[Var]): MagicWand =
      MagicWand(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ left.varSeq ++ right.varSeq

    override def toString: String = "(" + left + ") -* (" + right + ")"
  }

  final case class Septraction(guard: GslFormula, left: GslFormula, right: GslFormula) extends GslFormula {
    override type T = Septraction

    override def _substitute(substitution: Substitution[Var]): Septraction =
      Septraction(guard.substitute(substitution), left.substitute(substitution), right.substitute(substitution))

    override val predicateCalls: Set[String] = guard.predicateCalls union left.predicateCalls union right.predicateCalls
    override val varSeq: Seq[Var] = guard.varSeq ++ left.varSeq ++ right.varSeq

    override def toString: String = "(" + left + ") -o (" + right + ")"
  }

}