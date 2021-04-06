package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.Utils.SetUtils
import at.forsyte.harrsh.seplog.Var

import scala.collection.{SortedSet, mutable}

class AliasingConstraint(val domain: Set[Var], val partition: IndexedSeq[SortedSet[Var]]) {

  val eqClass: mutable.Map[Var, Int] = mutable.Map.empty

  require(Utils.isSorted(partition)(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))

  require(partition.flatten.toSet == domain)

  // TODO: disable for performance
  require(domain.size == partition.map(_.size).sum, "Partition is not valid")

  private def eqClassGet(v: Var): Int = {
    require(domain(v))

    if (eqClass.contains(v))
      eqClass(v)
    else {
      val index = partition.indexWhere(s => s.contains(v))
      require(index >= 0)
      eqClass.put(v, index)

      index
    }
  }

  def largestAlias(v: Var): Var = this (v).max

  def apply(v: Var): SortedSet[Var] = partition(eqClassGet(v))

  def =:=(left: Var, right: Var): Boolean = eqClassGet(left) == eqClassGet(right)

  def =/=(left: Var, right: Var): Boolean = !(this =:= (left, right))

  def subsetOf(other: AliasingConstraint): Boolean = {
    partition.forall(s => other.partition.exists(su => s.subsetOf(su)))
  }

  def allExtensions(v: Var): Set[AliasingConstraint] = {
    require(!domain(v))

    val newDomain = domain.incl(v)

    Set.from(partition.zipWithIndex.map({
      case (set, idx) => new AliasingConstraint(newDomain, partition.updated(idx, set.union(Set(v))).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))
    })).incl(new AliasingConstraint(newDomain, (partition :+ SortedSet(v)).sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var])))
  }

  def rename(subst: Map[Var, Var]): AliasingConstraint = {
    require(domain.disjoint(subst.values.toSet))

    val newPartition = partition.map(ss => ss.map(v => subst.getOrElse(v, v)))

    new AliasingConstraint(domain.map(i => subst.getOrElse(i, i)), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))
  }

  def remove(vars: Seq[Var]): AliasingConstraint = vars.foldLeft(this) { (ac, x) => ac.remove(x) }

  def remove(x: Var): AliasingConstraint = {
    require(domain.contains(x))
    require(this (x).size > 1)

    val newPartition = partition.map(_.filter(_ != x))

    new AliasingConstraint(domain.excl(x), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))
  }

  def reverseRenaming(x: Seq[Var], y: Seq[Var]): AliasingConstraint = {
    val xSet = x.toSet
    val ySet = y.toSet
    require(x.length == xSet.size)
    require(x.length == y.length)
    require(domain.intersect(xSet).isEmpty)

    require(ySet.subsetOf(domain))

    val yMap: Seq[(Int, Var)] = y.map(eqClassGet).zip(y)
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

    new AliasingConstraint(domain.union(xSet), newPartition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))
  }

  def restricted(v: Set[Var]): AliasingConstraint = {
    val partitionRemoved = partition.map(_.intersect(v))

    val partitionFiltered = partitionRemoved.filter(_.nonEmpty)

    new AliasingConstraint(domain.intersect(v), partitionFiltered.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]))
  }

  override def hashCode(): Int = {
    partition.hashCode()
  }

  override def equals(obj: Any): Boolean =
    obj match {
      case ac: AliasingConstraint =>
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

  def allAliasingConstraints(vars: Set[Var]): LazyList[AliasingConstraint] =
    allPartitions(vars).map(partition => new AliasingConstraint(vars, partition.map(v => SortedSet.from(v)).toIndexedSeq.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var])))

  def allPartitions[A](set: Set[A])(implicit ordering: Ordering[A]): LazyList[Set[Set[A]]] = {
    def aux(seq: Seq[A]): LazyList[Set[Set[A]]] = {
      seq match {
        case Seq() => LazyList(Set(Set.empty))
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