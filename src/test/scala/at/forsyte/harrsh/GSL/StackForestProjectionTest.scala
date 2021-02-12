package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet

class StackForestProjectionTest extends AnyFlatSpec {
  "StackForestProjection" should "correctly compute all rescopings" in {

    def P(pred: String)(vars: Var*): PredicateCall = {
      PredicateCall(pred, vars)
    }

    val x = FreeVar("x")
    val y = FreeVar("y")
    val z = FreeVar("z")
    val _1 = BoundVar(1)

    val left = StackForestProjection.from(SortedSet(_1),
      SortedSet(),
      Seq(TreeProjection(Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
        TreeProjection(Seq(), P("lseg")(z, _1))))

    val right = StackForestProjection.from(SortedSet(),
      SortedSet(_1),
      Seq(TreeProjection(Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    val result = StackForestProjection.from(SortedSet(_1),
      SortedSet(),
      Seq(TreeProjection(Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
        TreeProjection(Seq(), P("lseg")(z, _1)),
        TreeProjection(Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    StackForestProjection.allRescopings(left, right).foreach(println(_))

    assert(StackForestProjection.allRescopings(left, right).contains(result))
  }
}
