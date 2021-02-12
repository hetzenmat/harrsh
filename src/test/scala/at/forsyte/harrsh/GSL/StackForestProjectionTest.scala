package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}
import org.scalatest.flatspec.AnyFlatSpec

class StackForestProjectionTest extends AnyFlatSpec {
  "StackForestProjection" should "correctly compute all rescopings" in {

    def P(pred: String)(vars: Var*): PredicateCall = {
      PredicateCall(pred, vars)
    }

    val x = FreeVar("x")
    val y = FreeVar("y")
    val z = FreeVar("z")
    val _1 = BoundVar(1)

    val left = StackForestProjection(Seq(_1),
      Seq(),
      Seq((Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
        (Seq(), P("lseg")(z, _1))))

    val right = StackForestProjection(Seq(),
      Seq(_1),
      Seq((Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    val result = StackForestProjection(Seq(_1),
      Seq(),
      Seq((Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
        (Seq(), P("lseg")(z, _1)),
        (Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    assert(StackForestProjection.allRescopings(left, right).contains(result))
  }
}
