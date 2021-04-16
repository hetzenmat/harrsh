package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}
import com.typesafe.scalalogging.LazyLogging

import java.util.Scanner

class TypeComputation(val sid: SID_btw, val formula: GslFormula) extends LazyLogging {

  val predicateTypes = new PredicateTypes(sid, formula.freeVars)

  sealed trait Quantifier {
    def test[A](coll: Iterable[A], p: A => Boolean): Boolean
  }

  case object Exists extends Quantifier {
    override def test[A](coll: Iterable[A], p: A => Boolean): Boolean = coll.exists(p)
  }

  case object Forall extends Quantifier {
    override def test[A](coll: Iterable[A], p: A => Boolean): Boolean = coll.forall(p)
  }

  private def magicWandSeptractionHelper(q: Quantifier,
                                         ac: AliasingConstraint[Var],
                                         guard: GslFormula,
                                         left: GslFormula,
                                         right: GslFormula): Set[PhiType] = {
    val guardTypes = types(guard, ac)
    val leftTypes = types(left, ac)
    val rightTypes = types(right, ac)

    guardTypes.filter(phiType => q.test(leftTypes, (leftType: PhiType) => PhiType.composition(sid, phiType, leftType, ac) match {
      case Some(compositionType) => rightTypes contains compositionType
      case None => false
    }))
  }

  def types(ac: AliasingConstraint[Var]): Set[PhiType] = types(formula, ac)

  def _reduce(types: Set[PhiType]): Set[PhiType] = {

    types.find(typ => types.excl(typ).exists(other => typ.projections.subsetOf(other.projections))) match {
      case Some(typ) => _reduce(types.excl(typ))
      case None => types
    }


  }

  private def types(gslFormula: GslFormula, ac: AliasingConstraint[Var]): Set[PhiType] = gslFormula match {
    case atom: Atom => atom match {
      case Atom.Emp() => Set(PhiType.empty)
      case e: Equality => TypeComputation.equality(e, ac)
      case d: DisEquality => TypeComputation.disEquality(d, ac)
      case p: PointsTo => TypeComputation.pointsTo(p, ac, sid)
      case PredicateCall(predName, args) =>
        val pred = sid.predicates(predName)
        val types = predicateTypes.getTypeLazy(pred, ac.reverseRenaming(pred.args.map(FreeVar), args))

        PhiType.rename(pred.args.map(FreeVar), args, ac, types, sid).toSet
    }
    case GslFormula.SeparatingConjunction(left, right) =>
      val leftTypes = types(left, ac)
      val rightTypes = types(right, ac)

      val composition = PhiType.composition(sid, leftTypes, rightTypes, ac).toSet

      println(gslFormula)
      println(leftTypes)
      println(rightTypes)
      println("Comp: " + composition)

      composition


    case GslFormula.StandardConjunction(left, right) =>
      val typesLeft = types(left, ac)
      val typesRight = types(right, ac)

      val result = typesLeft intersect typesRight
      println("Left: " + typesLeft)
      println("Right: " + typesRight)
      println("Result: " + result)

      result

    case GslFormula.Disjunction(left, right) => types(left, ac) union types(right, ac)
    case GslFormula.Negation(guard, negated) =>
      val guardTypes = types(guard, ac)
      val negatedTypes = types(negated, ac)

      println(gslFormula)
      val guardSorted = guardTypes.toSeq.sorted
      val negatedSorted = negatedTypes.toSeq.sorted
      println("Guard:   " + guardSorted)
      println("Negated: " + negatedSorted)

      println()
      println("Guard Enumeration: ")
      for ((t, i) <- guardSorted.zipWithIndex) {
        println((i + 1) + ": " + t)
      }

      println("\nNegated Enumeration: ")
      for ((t, i) <- negatedSorted.zipWithIndex) {
        println((i + 1) + ": " + t)
      }

      val allLeft = guardTypes.flatMap(_.projections.unsorted)
      val allRight = negatedTypes.flatMap(_.projections.unsorted)

      val l = allLeft.diff(allRight).toSeq.sorted
      println("Left all: " + l)

      val r = guardTypes diff negatedTypes

      val rSorted = r.toSeq.sorted
      println("Result: " + rSorted)

//      val s = new Scanner(System.in)
//      println("Enter to continue")
//      s.nextLine()

      r
    case GslFormula.MagicWand(guard, left, right) => magicWandSeptractionHelper(Forall, ac, guard, left, right)
    case GslFormula.Septraction(guard, left, right) => magicWandSeptractionHelper(Exists, ac, guard, left, right)
  }
}

object TypeComputation {
  def equality(eq: Equality, ac: AliasingConstraint[Var]): Set[PhiType] = if (ac =:= (eq.left, eq.right)) Set(PhiType.empty) else Set()

  def disEquality(disEq: DisEquality, ac: AliasingConstraint[Var]): Set[PhiType] = if (ac =:= (disEq.left, disEq.right)) Set() else Set(PhiType.empty)

  def pointsTo(pointsTo: PointsTo, ac: AliasingConstraint[Var], sid: SID_btw): Set[PhiType] =
    if (ac =:= (pointsTo.from, NullConst)) {
      Set.empty
    } else {
      val r = Set(PhiType.ptrmodel(sid, ac, pointsTo).substitute(Substitution.from(ac.domain.map(v => (v, AliasingConstraint.largestAlias(ac, v))))))
      r
    }
}