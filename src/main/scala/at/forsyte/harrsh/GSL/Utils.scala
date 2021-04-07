package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{NullConst, Var}

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq

object Utils {

  implicit class SetUtils[A](val s: Set[A]) {
    def disjoint(other: Set[A]): Boolean = s.intersect(other).isEmpty
  }

  def nonCanonical(t: Iterable[PhiType], ac: AliasingConstraint[Var]): Boolean =
    t.exists(t => nonCanonicalSF(t.projections, ac))

  def nonCanonical(t: PhiType, ac: AliasingConstraint[Var]): Boolean =
    nonCanonicalSF(t.projections, ac)

  def nonCanonicalSF(s: Iterable[StackForestProjection], ac: AliasingConstraint[Var]): Boolean =
    s.exists(sf => sf.freeVars.asInstanceOf[Set[Var]].exists(v => AliasingConstraint.largestAlias(ac, v) != v))

  def compareLexicographically[A](a: Seq[A], b: Seq[A])(implicit evidence: A => Ordered[A]): Int = {
    val res = a.zip(b).collectFirst({
      case (v1, v2) if v1 < v2 => -1
      case (v1, v2) if v1 > v2 => 1
    })
    res match {
      case None => a.size.compareTo(b.size)
      case Some(x) => x
    }
  }

  def allAssignments[A, B](elems: Seq[A], values: Seq[B]): Seq[Seq[(A, B)]] = {
    require(values.nonEmpty)
    require(elems.nonEmpty)

    def aux(elems: Seq[A]): Seq[Seq[(A, B)]] = {
      elems match {
        case Seq(a) => values.map(v => Seq((a, v)))
        case head +: tail => values.flatMap(i => aux(tail).map(v => (head, i) +: v))
      }
    }

    aux(elems)
  }

  def allAssignments[A](length: Int, values: Seq[A]): Seq[Seq[A]] = {
    require(values.nonEmpty)

    def aux(length: Int): Seq[Seq[A]] =
      length match {
        case 1 => values.map(v => Seq(v))
        case _ => values.flatMap(i => aux(length - 1).map(i +: _))
      }

    aux(length)
  }

  def allSeqsWithRange(length: Int, range: Range): LazyList[Seq[Int]] = length match {
    case 1 => LazyList.from(range.map(i => Seq(i)))
    case _ => LazyList.from(range.flatMap(i => allSeqsWithRange(length - 1, range).map(i +: _)))
  }

  def isSorted[A](a: Seq[A])(implicit evidence: Ordering[A]): Boolean = {
    if (a.isEmpty)
      true
    else
      a.zip(a.tail).forall(t => evidence.lteq(t._1, t._2))
  }
}
