package at.forsyte.harrsh.GSL

import scala.collection.SortedSet
import scala.math.Ordering.Implicits.sortedSetOrdering

class AliasingConstraint {
}

object AliasingConstraint {
  def allPartitions[A](set: SortedSet[A])(implicit ordering: Ordering[A]): LazyList[SortedSet[SortedSet[A]]] = {
    if (set.size <= 1) {
      LazyList(SortedSet(set))
    } else {
      val elem = set.head
      val partitions = allPartitions(set.tail)
      partitions.flatMap((partition: SortedSet[SortedSet[A]]) => {
        LazyList(partition + SortedSet(elem)) ++ partition.foldLeft(LazyList.empty[SortedSet[SortedSet[A]]]) { (seq, set) =>
          seq.appended((partition - set) + (set + elem))
        }
      })
    }
  }
}