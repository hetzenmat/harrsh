package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{NullConst, Var}

object Utils {

  implicit class SetUtils[A](val s: Set[A]) {
    def disjoint(other: Set[A]): Boolean = s.intersect(other).isEmpty
  }

  def nonCanonical(t: Iterable[PhiType], ac: AliasingConstraint): Boolean =
    t.exists(t => nonCanonicalSF(t.projections, ac))

  def nonCanonical(t: PhiType, ac: AliasingConstraint): Boolean =
    nonCanonicalSF(t.projections, ac)

  def nonCanonicalSF(s: Iterable[StackForestProjection], ac: AliasingConstraint): Boolean =
    s.exists(sf => sf.freeVars.asInstanceOf[Set[Var]].exists(v => ac.largestAlias(v) != v))

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
