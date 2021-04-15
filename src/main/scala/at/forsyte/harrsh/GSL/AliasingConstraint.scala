package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.Utils.SetUtils
import at.forsyte.harrsh.seplog.{NullConst, Var}

import scala.collection.{SortedSet, mutable}

class AliasingConstraint[T](val domain: Set[T], val partition: IndexedSeq[SortedSet[T]])(implicit ord: Ordering[T]) {

  val eqClass: mutable.Map[T, Int] = mutable.Map.empty

  Utils.debugRequire(Utils.isSorted(partition)(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
  Utils.debugRequire(partition.flatten.toSet == domain)
  Utils.debugRequire(partition.forall(_.nonEmpty))

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

  def isLone(v: T): Boolean = this(v).size == 1

  def getEquivalenceClass(v: T): SortedSet[T] = this(v)

  private def apply(v: T): SortedSet[T] = partition(eqClassGet(v))

  def =:=(left: T, right: T): Boolean = eqClassGet(left) == eqClassGet(right)

  def =/=(left: T, right: T): Boolean = !(this =:= (left, right))

  def subsetOf(other: AliasingConstraint[T]): Boolean = {
    partition.forall(s => other.partition.exists(su => s.subsetOf(su)))
  }

  def allExtensions(v: T): Set[AliasingConstraint[T]] = {
    Utils.debugRequire(!domain(v))

    val newDomain = domain.incl(v)

    Set.from(partition.zipWithIndex.map({
      case (set, idx) => new AliasingConstraint(newDomain, partition.updated(idx, set.union(Set(v))).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
    })).incl(new AliasingConstraint(newDomain, (partition :+ SortedSet(v)).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T])))
  }

  def rename(subst: Map[T, T]): AliasingConstraint[T] = {
    Utils.debugRequire(domain.disjoint(subst.values.toSet))

    val newPartition = partition.map(ss => ss.map(v => subst.getOrElse(v, v)))

    new AliasingConstraint(domain.map(i => subst.getOrElse(i, i)), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
  }

  def remove(elems: Seq[T]): AliasingConstraint[T] = elems.foldLeft(this) { (ac, x) => ac.remove(x) }

  def remove(x: T): AliasingConstraint[T] = {
    Utils.debugRequire(domain.contains(x))
    Utils.debugRequire(this (x).size > 1)

    val newPartition = partition.map(_.filter(_ != x))

    new AliasingConstraint(domain.excl(x), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
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

    new AliasingConstraint(domain.union(xSet), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
  }

  def restricted(v: Set[T]): AliasingConstraint[T] = {
    val partitionRemoved = partition.map(_.intersect(v))

    val partitionFiltered = partitionRemoved.filter(_.nonEmpty)

    new AliasingConstraint(domain.intersect(v), partitionFiltered.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
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
    val eq = domain.toSeq.sorted.map(v => v + " -> " + eqClassGet(v)).mkString(" ")

    part + " " + eq
  }
}

object AliasingConstraint {

  def largestAlias(ac: AliasingConstraint[Var], v: Var): Var = {
    if (ac.domain.contains(NullConst) && ac =:= (v, NullConst)) NullConst
    else ac(v).max
  }

  def largestAliasInt(ac: AliasingConstraint[Int], v: Int): Int = {
    if (ac.domain.contains(0) && ac =:= (v, 0)) 0
    else ac(v).max
  }

  def allAliasingConstraints[T](elems: Set[T])(implicit ord: Ordering[T]): LazyList[AliasingConstraint[T]] =
    allPartitions(elems).map { partition =>
      new AliasingConstraint(elems,
                             partition.map(v => SortedSet.from(v)).toIndexedSeq.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, T]))
    }

  def allPartitions[A](set: Set[A])(implicit ordering: Ordering[A]): LazyList[Set[Set[A]]] = {
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

    aux(set.toSeq.sorted)
  }
}