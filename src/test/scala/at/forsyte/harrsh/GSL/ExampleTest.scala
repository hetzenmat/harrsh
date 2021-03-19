package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SIDs.parseFormula
import org.scalatest.flatspec.AnyFlatSpec

class ExampleTest extends AnyFlatSpec {
  "Type computation" should "correctly decide satisfiability of formulas in 'Example 4.1'" in {
    Query(parseFormula("lseg(x, y) /\\ ~x -> y"), SIDs.lseg).isSatisfiable match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }

    // TODO: verify
    Query(parseFormula("lseg(x, y) /\\ (lseg(y, z) -o lseg(x, x))"), SIDs.lseg).isSatisfiable match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }
  }

}
