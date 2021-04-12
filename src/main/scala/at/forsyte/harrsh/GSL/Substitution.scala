package at.forsyte.harrsh.GSL

class Substitution[A] private(val map: collection.mutable.Map[A, A]) {
  def add(t: (A, A)): Unit = add(t._1, t._2)

  def add(from: A, to: A): Unit = {
    require(!map.isDefinedAt(from) || map(from) == to)

    map.put(from, to)
  }

  def isDefinedAt: A => Boolean = map.isDefinedAt

  def apply(value: A): A = map.getOrElse(value, value)

  def filter(pred: ((A, A)) => Boolean): Substitution[A] = {
    new Substitution(map.filter(pred))
  }

  def filterKeys(pred: A => Boolean): Substitution[A] = {
    val f: ((A, A)) => Boolean = {
      case (k, _) => pred(k)
    }

    new Substitution(map.filter(f))
  }
}

object Substitution {

  @inline
  def empty[A]: Substitution[A] = new Substitution(collection.mutable.Map.empty[A, A])

  def from[A](elems: Seq[(A, A)]): Substitution[A] = {
    val s = empty[A]
    elems.foreach(s.add)

    s
  }
}
