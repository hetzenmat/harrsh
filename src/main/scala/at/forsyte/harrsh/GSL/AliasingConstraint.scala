package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.Var

import scala.collection.SortedSet

case class AliasingConstraint(domain: SortedSet[Var], partition: Map[Var, Var]) {
  if (domain != partition.keySet)
    throw new IllegalArgumentException("Inconsistent domains")

  def =:=(t: (Var, Var)): Boolean = domain.contains(t._1) && domain.contains(t._2) && partition(t._1) == partition(t._2)

  def =/=(t: (Var, Var)): Boolean = !(this =:= t)
}

object AliasingConstraint {

  def allAliasingConstraints(vars: Set[Var]): LazyList[AliasingConstraint] = {
    allPartitions(vars).map(p => AliasingConstraint(SortedSet.from(vars), p))
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