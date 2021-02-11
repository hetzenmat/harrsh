package at.forsyte.harrsh.GSL

import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet
import scala.math.Ordering.Implicits.sortedSetOrdering

class AliasingConstraintTest extends AnyFlatSpec {
  "AliasingConstraint" should "correctly compute set partitions" in {
    val part3 = AliasingConstraint.allPartitions(SortedSet(1, 2, 3))

    assert(part3.size == 5)

    assert(part3 == Seq(SortedSet(SortedSet(1), SortedSet(2), SortedSet(3)),
      SortedSet(SortedSet(1, 2), SortedSet(3)),
      SortedSet(SortedSet(1, 3), SortedSet(2)),
      SortedSet(SortedSet(1), SortedSet(2, 3)),
      SortedSet(SortedSet(1, 2, 3))))

    assert(AliasingConstraint.allPartitions(SortedSet.from(1 to 10)).size == 115975)
  }
}
