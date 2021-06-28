package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{FreeVar, Var}
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet

class AliasingConstraintTest extends AnyFlatSpec {
  "AliasingConstraint" should "correctly compute set partitions" in {
    assert(AliasingConstraint.allPartitions(Set.from(1 to 4)).size == 15)
    assert(AliasingConstraint.allPartitions(Set.from(1 to 10)).size == 115975)
  }

  it should "correctly determine equalities between variables" in {
    val (a, b, c): (FreeVar, FreeVar, FreeVar) = (FreeVar("a"), FreeVar("b"), FreeVar("c"))
    val ac = new AliasingConstraint[Var](Set(a, b, c), IndexedSeq(SortedSet(a), SortedSet(b, c)))

    assert(a < b && a < c && b < c)

    assert(ac =:= (a, a))
    assert(ac =/= (a, b))
    assert(ac =/= (b, a))
    assert(ac =/= (a, c))
    assert(ac =/= (c, a))
    assert(ac =:= (b, b))
    assert(ac =:= (b, c))
    assert(ac =:= (c, b))
    assert(ac =:= (c, c))

    for (v <- Seq(a, b, c)) {
      assert(ac =:= (v, v))
    }

    assert(ac.largestAlias(b) == c)

    for (e1 <- Seq(a, b, c);
         e2 <- Seq(a, b, c)) {
      assert((ac =:= (e1, e2)) == !(ac =/= (e1, e2)))
    }

    val vars: Set[Var] = Set(a, b, c)
    for (ac <- AliasingConstraint.allAliasingConstraints(vars);
         v1 <- vars;
         v2 <- vars) {
      assert(!(ac =:= (v1, v2)) || (ac =:= (v2, v1)))
    }
  }

  it should "reject inconsistent domains" in {
    assertThrows[IllegalArgumentException] {
      new AliasingConstraint[Var](Set(FreeVar("a")), IndexedSeq())
    }
  }
}
