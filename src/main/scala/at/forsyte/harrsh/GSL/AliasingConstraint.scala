package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.AliasingConstraint.ACOrdering
import at.forsyte.harrsh.GSL.Utils.SetUtils
import at.forsyte.harrsh.seplog.{NullConst, Var}

import scala.collection.{SortedSet, mutable}

class AliasingConstraint[T](val domain: Set[T], val partition: IndexedSeq[SortedSet[T]])(implicit ord: ACOrdering[T]) {

  val eqClass: mutable.Map[T, Int] = mutable.Map.empty

  Utils.debugRequire(Utils.isSorted(partition)(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
  Utils.debugRequire(partition.flatten.toSet == domain)
  Utils.debugRequire(partition.forall(_.nonEmpty))
  Utils.debugRequire(
    (for (i <- 0 until partition.size - 1;
          j <- i + 1 until partition.size) yield
      partition(i).intersect(partition(j)).isEmpty
      ).forall(identity))

  private def eqClassGet(v: T): Int = {
    Utils.debugRequire(domain(v))

    if (eqClass.contains(v))
      eqClass(v)
    else {
      val index = partition.indexWhere(s => s.contains(v))
      Utils.debugRequire(index >= 0)
      eqClass.put(v, index)

      index
    }
  }

  def isLone(v: T): Boolean = this (v).size == 1

  def getEquivalenceClass(v: T): SortedSet[T] = this (v)

  private def apply(v: T): SortedSet[T] = partition(eqClassGet(v))

  def largestAlias(v: T): T = this (v).max(ord.ordering)

  def =:=(left: T, right: T): Boolean = eqClassGet(left) == eqClassGet(right)

  def =/=(left: T, right: T): Boolean = !(this =:= (left, right))

  def subsetOf(other: AliasingConstraint[T]): Boolean = {
    partition.forall(s => other.partition.exists(su => s.subsetOf(su)))
  }

  def allExtensionsIt(v: Iterable[T]): Set[AliasingConstraint[T]] = {
    assert(v.nonEmpty)

    v.foldLeft(Set(this))((acs, v) => acs.flatMap(_.allExtensions(v)))
  }

  def allExtensions(v: T): Set[AliasingConstraint[T]] = {
    Utils.debugRequire(!domain(v))

    val newDomain = domain.incl(v)

    Set.from(partition.zipWithIndex.map({
      case (set, idx) => new AliasingConstraint(newDomain, partition.updated(idx, set.union(Set(v))).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
    }) :+ new AliasingConstraint(newDomain, (partition :+ SortedSet(v)(ord.ordering)).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering))))
  }

  def rename(subst: Map[T, T]): AliasingConstraint[T] = {
    assert(subst.keySet.subsetOf(domain))
    assert(domain.disjoint(subst.values.toSet))

    val newPartition = partition.map(ss => ss.map(v => subst.getOrElse(v, v))(ord.ordering))

    new AliasingConstraint(domain.map(i => subst.getOrElse(i, i)), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
  }

  def remove(elems: Seq[T]): AliasingConstraint[T] = elems.foldLeft(this) { (ac, x) => ac.remove(x) }

  def remove(x: T): AliasingConstraint[T] = {
    Utils.debugRequire(domain.contains(x))
    Utils.debugRequire(this (x).size > 1)

    val newPartition = partition.map(_.filter(_ != x))

    new AliasingConstraint(domain.excl(x), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
  }

  def reverseRenaming(x: Seq[T], y: Seq[T]): AliasingConstraint[T] = {
    val xSet = x.toSet
    val ySet = y.toSet
    Utils.debugRequire(x.length == xSet.size)
    Utils.debugRequire(x.length == y.length)
    Utils.debugRequire(domain.intersect(xSet).isEmpty)

    Utils.debugRequire(ySet.subsetOf(domain))

    val yMap: Seq[(Int, T)] = y.map(eqClassGet).zip(y)
    val toChange = yMap.map(_._1).toSet
    val rel = x.zip(y)

    val newPartition = partition.zipWithIndex.map({
      case (set, idx) =>
        if (toChange contains idx) {
          set.union(Set.from(rel.filter({ case (_, yy) => yMap.exists(t => t._1 == idx && t._2 == yy) }).map(_._1)))
        } else {
          set
        }
    })

    new AliasingConstraint(domain.union(xSet), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
  }

  def restricted(v: Set[T]): AliasingConstraint[T] = {
    val partitionRemoved = partition.map(_.intersect(v))

    val partitionFiltered = partitionRemoved.filter(_.nonEmpty)

    new AliasingConstraint(domain.intersect(v), partitionFiltered.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
  }

  override def hashCode(): Int = {
    partition.hashCode()
  }

  override def equals(obj: Any): Boolean =
    obj match {
      case ac: AliasingConstraint[T] =>
        partition == ac.partition

      case _ => false
    }

  override def toString: String = {

    val part = partition.map(p => p.mkString("{", ", ", "}")).mkString(" ")
    val eq = domain.toSeq.sorted(ord.ordering).map(v => v + " -> " + eqClassGet(v)).mkString(" ")

    part + " " + eq
  }
}

object AliasingConstraint {

  sealed trait ACOrdering[T] {
    val ordering: Ordering[T]
  }

  implicit object ACIntOrdering extends ACOrdering[Int] {
    override val ordering: Ordering[Int] =
      (x: Int, y: Int) =>
        if (x < 0 || y < 0) throw new IllegalArgumentException("Aliasing Constraints should only work with natural numbers")
        else if (x == y) 0
        else if (x == 0) 1 // 0 (i.e., the null pointer shall be the biggest element)
        else if (y == 0) -1
        else x.compare(y)
  }

  implicit object ACVarOrdering extends ACOrdering[Var] {
    override val ordering: Ordering[Var] = {
      case (x, y) if x.equals(y) => 0
      case (NullConst, _) => 1
      case (_, NullConst) => -1
      case (x, y) => x.compare(y)
    }
  }

  def allAliasingConstraints[T](elems: Set[T])(implicit ord: ACOrdering[T]): LazyList[AliasingConstraint[T]] =
    allPartitions(elems).map { partition =>
      new AliasingConstraint(elems,
                             partition.map(v => SortedSet.from(v)(ord.ordering)).toIndexedSeq.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T](ord.ordering)))
    }

  def allPartitions[A](set: Set[A])(implicit ord: ACOrdering[A]): LazyList[Set[Set[A]]] = {
    def aux(seq: Seq[A]): LazyList[Set[Set[A]]] = {
      seq match {
        case Seq() => LazyList(Set.empty)
        case Seq(e) => LazyList(Set(Set(e)))
        case Seq(head, tail@_*) =>
          val partitions = aux(tail)

          partitions.flatMap(sets => {
            LazyList(sets.incl(Set(head))) ++ sets.map((e: Set[A]) => sets.excl(e).incl(e.incl(head)))
          })
      }
    }

    aux(set.toSeq.sorted(ord.ordering))
  }
}