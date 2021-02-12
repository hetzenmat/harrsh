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

  def isSorted[A](a: Seq[A])(implicit evidence: A => Ordered[A]): Boolean = {
    if (a.isEmpty)
      true
    else
      a.zip(a.tail).forall(t => t._1 < t._2)
  }
}
