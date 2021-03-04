package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.Utils.SetUtils
import at.forsyte.harrsh.seplog.Var

import scala.collection.SortedSet
import scala.collection.mutable.ListBuffer
import scala.runtime.ScalaRunTime

class AliasingConstraint(val partition: Seq[SortedSet[Var]], val eqClass: Map[Var, Int]) {

  val domain: Set[Var] = eqClass.keySet

  require(domain.size == partition.map(_.size).sum, "Partition is not valid")

  require(eqClass.values.forall(i => i >= 0 && i < partition.length), "Index out of bounds")

  require(eqClass.forall({ case (k, v) => partition(v).contains(k) }), "Equivalence mapping is not valid")

  def largestAlias(v: Var): Var = eqClass.get(v) match {
    case Some(value) => partition(value).max
    case None => v
  }

  def apply(v: Var): SortedSet[Var] = partition(eqClass(v))

  def =:=(left: Var, right: Var): Boolean = eqClass(left) == eqClass(right)

  def =/=(left: Var, right: Var): Boolean = !(this =:= (left, right))

  def subsetOf(other: AliasingConstraint): Boolean = {
    partition.forall(s => other.partition.exists(su => s.subsetOf(su)))
  }

  def allExtensions(v: Var): Set[AliasingConstraint] = {
    Set.from(partition.zipWithIndex.map({
      case (set, idx) => new AliasingConstraint(partition.updated(idx, set.union(Set(v))), eqClass.updated(v, idx))
    })).incl(new AliasingConstraint(partition :+ SortedSet(v), eqClass.updated(v, partition.size)))
  }

  def rename(subst: Map[Var, Var]): AliasingConstraint = {
    require(domain.disjoint(subst.values.toSet))

    val newPartition = partition.map(ss => ss.map(v => subst.getOrElse(v, v)))
    val newEqClass = eqClass.map(kv => (subst.getOrElse(kv._1, kv._1), kv._2))

    new AliasingConstraint(newPartition, newEqClass)
  }

  def reverseRenaming(x: Seq[Var], y: Seq[Var]): AliasingConstraint = {
    val xSet = x.toSet
    val ySet = y.toSet
    require(x.length == xSet.size)
    require(x.length == y.length)
    require(domain.intersect(xSet).isEmpty)

    require(ySet.subsetOf(domain))

    val yMap: Seq[(Int, Var)] = y.map(eqClass).zip(y)
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

    val newEqClass = (eqClass.toSeq ++ rel.map({ case (xx, yy) => (xx, eqClass(yy)) })).toMap

    new AliasingConstraint(newPartition, newEqClass)
  }

  def restricted(v: Set[Var]): AliasingConstraint = {
    val partitionRemoved = partition.map(_.intersect(v))
    val eqClassFiltered = eqClass.filter(t => v.contains(t._1))

    val emptySetsIndices = partitionRemoved.zipWithIndex.filter(_._1.isEmpty).map(_._2)

    val partitionFiltered = partitionRemoved.filter(_.nonEmpty)

    val eqClassReordered = eqClassFiltered.map({ case (k, idx) =>
      (k, idx - emptySetsIndices.count(_ < idx))
    })

    new AliasingConstraint(partitionFiltered, eqClassReordered)
  }

  override def hashCode(): Int = {

    partition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]).hashCode()
  }


  override def equals(obj: Any): Boolean =
    obj match {
      case ac: AliasingConstraint =>

        partition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var]) == ac.partition.sorted(scala.Ordering.Implicits.sortedSetOrdering[SortedSet, Var])


      //        if (domain != ac.domain) return false
      //
      //        for (varA <- domain;
      //             varB <- domain) {
      //          if ((this =:= (varA, varB)) != (ac =:= (varA, varB))) {
      //            return false
      //          }
      //        }
      //
      //        true
      case _ => false
    }

  override def toString: String = {

    val part = partition.map(p => p.mkString("{", ", ", "}")).mkString(" ")
    val eq = domain.toSeq.sorted.map(v => v + " -> " + eqClass(v)).mkString(" ")

    part + " " + eq
  }
}

object AliasingConstraint {

  def allAliasingConstraints(vars: Set[Var]): LazyList[AliasingConstraint] = {
    allPartitions(vars).map(eqClass => {

      val buffer = ListBuffer.empty[collection.mutable.Set[Var]]
      val map = collection.mutable.Map.empty[Var, Int]
      eqClass.foreach({ case (variable, repr) =>

        map.get(repr) match {
          case Some(index) =>
            buffer(index).add(variable)
            map.update(variable, index)
          case None =>
            buffer.addOne(collection.mutable.Set(variable, repr))
            map.update(repr, buffer.size - 1)
            map.update(variable, buffer.size - 1)
        }
      })

      new AliasingConstraint(buffer.map(s => SortedSet.from(s)).toSeq, map.toMap)
    })
  }

  def mapRepresentationToSet[A](partition: Map[A, A]): Set[Set[A]] = {
    partition.foldLeft(Set(): Set[Set[A]]) { case (set, (k, v)) =>
      set.find(_.contains(v)) match {
        case None => set.incl(Set(k, v))
        case Some(eq) => set.excl(eq).incl(eq.incl(k))
      }
    }
  }

  def allPartitions[A](set: Set[A])(implicit ordering: Ordering[A]): LazyList[Map[A, A]] = {

    def help(seq: Seq[A]): LazyList[Map[A, A]] = {
      seq match {
        case Seq() => LazyList(Map.empty)
        case Seq(e) => LazyList(Map(e -> e))
        case Seq(head, tail@_*) =>
          // first is < than all in tail
          val partitions = help(tail)
          partitions.flatMap(map => {
            val first = map.updated(head, head)

            LazyList(first) ++ map.values.toSet.map((e: A) => map.updated(head, e))
          })
      }
    }

    val ordered = set.toSeq.sorted
    help(ordered)
  }
}