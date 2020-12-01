package at.forsyte.harrsh.pure

import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.seplog._
import at.forsyte.harrsh.seplog.inductive.PureAtom
import at.forsyte.harrsh.util.Combinators

import scala.annotation.tailrec

/**
  * Created by jkatelaa on 5/16/17.
  */
object ConstraintPropagation extends HarrshLogging {

  def propagateConstraints(alloc: Set[Var], pure: Set[PureAtom]): (Set[Var], Set[PureAtom]) = {

    val allPure = propagateConstraints(pure)
    // Propagate equalities to allocation info
    val allocFromEqualities: Set[Var] = closeSetUnderEqualities(alloc, allPure)

    (allocFromEqualities, allPure)
  }

  def pairs[A](s: Set[A]): Set[(A, A)] = {
    if (s.nonEmpty) {
      val first = s.iterator.next()
      val ss = s.excl(first)

      (for {e <- ss} yield (first, e)).union(pairs(ss))
    } else {
      Set.empty
    }
  }

  @tailrec
  def propagateConstraints(from: Set[PureAtom]): Set[PureAtom] = {
    // TODO This function is inefficient

    val from_ : Set[PureAtom] = from.map(EqualityUtils.orderedAtom)

    val newEqs: Set[PureAtom] = pairs(from_) map {
      case (l, r) => transitiveConstraint(l, r)
    } filter (_.isDefined) map (_.get)

    val combined = from_.union(newEqs)
    if (combined == from_) from_ else propagateConstraints(combined)
  }

  private def transitiveConstraint(fvA: PureAtom, fvB: PureAtom): Option[PureAtom] = {

    val PureAtom(leftA, rightA, isEqualA) = fvA
    val PureAtom(leftB, rightB, isEqualB) = fvB

    if (isEqualA || isEqualB) {
      // If at least one is an equality, and one end of the eqs coincides, we can propagate
      val newPair: Option[(Var, Var)] =
        if (leftA == leftB) Some((rightA, rightB))
        else if (leftA == rightB) Some((rightA, leftB))
        else if (rightA == leftB) Some((leftA, rightB))
        else if (rightA == rightB) Some((leftA, leftB))
        else None

      newPair map (p => EqualityUtils.orderedAtom(p._1, p._2, isEqualA && isEqualB))
    }
    else {
      // Can't infer anything if both are inequalities
      None
    }
  }

  def closeSetUnderEqualities(explicit: Set[Var], allPure: Iterable[PureAtom]): Set[Var] = {
    closeSetUnderEqualitiesAux(explicit, allPure.filter(_.isEquality).toSeq, explicit)
  }

  @tailrec
  private def closeSetUnderEqualitiesAux(explicit: Set[Var], allPure: Seq[PureAtom], acc: Set[Var]): Set[Var] = {
    if (allPure.isEmpty) acc else {
      val hd = allPure.head
      val (l, r) = (hd.l, hd.r)
      val newAcc = if (explicit.contains(l)) acc + r else if (explicit.contains(r)) acc + l else acc
      closeSetUnderEqualitiesAux(explicit, allPure.tail, newAcc)
    }
  }

}
