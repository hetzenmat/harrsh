package at.forsyte.harrsh.GSL

object Utils {
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

  def isSorted[A](a: Seq[A])(implicit evidence: A => Ordered[A]): Boolean = {
    if (a.isEmpty)
      true
    else
      a.zip(a.tail).forall(t => t._1 <= t._2)
  }
}
