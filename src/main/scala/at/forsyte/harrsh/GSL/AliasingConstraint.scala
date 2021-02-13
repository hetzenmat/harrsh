package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.Var

import scala.collection.SortedSet
import scala.collection.mutable.ListBuffer

case class AliasingConstraint(partition: Seq[SortedSet[Var]], eqClass: Map[Var, Int]) {

  def domain: Set[Var] = eqClass.keySet

  require(domain.size == partition.map(_.size).sum, "Partition is not valid")

  require(eqClass.values.forall(i => i >= 0 && i < partition.length), "Index out of bounds")

  require(eqClass.forall({ case (k, v) => partition(v).contains(k) }), "Equivalence mapping is not valid")

  def largestAlias(v: Var): Var = this (v).max

  def apply(v: Var): SortedSet[Var] = partition(eqClass(v))

  def =:=(t: (Var, Var)): Boolean = eqClass(t._1) == eqClass(t._2)

  def =/=(t: (Var, Var)): Boolean = !(this =:= t)
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

      AliasingConstraint(buffer.map(s => collection.immutable.SortedSet.from(s)).toSeq, map.toMap)
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