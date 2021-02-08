package at.forsyte.harrsh.parsers

import at.forsyte.harrsh.GSL.GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula._
import at.forsyte.harrsh.seplog.{FreeVar, NullConst}
import org.scalatest.flatspec.AnyFlatSpec

class GslParserTest extends AnyFlatSpec {
  "GSL parser" should "parse valid inputs" in {

    val a = FreeVar("a")
    val b = FreeVar("b")
    val c = FreeVar("c")

    val valid = List(
      ("""a = a /\ (((((emp) -* emp))))""", MagicWand(Equality(a, a), Emp(), Emp())),
      ("emp", Emp()),
      ("((((     emp    )  )  )     )", Emp()),
      ("""a = b /\ b != c \/ a = c * a -> <b, null, null>""", SeparatingConjunction(Disjunction(StandardConjunction(Equality(a, b), DisEquality(b, c)), Equality(a, c)), PointsTo(a, Vector(b, NullConst, NullConst)))),
      ("""emp /\ ((a = b -* test(x1, null) ))""", MagicWand(Emp(), Equality(a, b), PredicateCall("test", Vector(FreeVar("x1"), NullConst)))),
      ("""((a = b -* test(x1, null) )) /\ ((emp))""", MagicWand(Emp(), Equality(a, b), PredicateCall("test", Vector(FreeVar("x1"), NullConst)))),
      ("""a = c /\ ~emp""", Negation(Equality(a, c), Emp()))
    )

    for ((input, expected) <- valid) {
      val parser = new GslParser(input)
      val result = parser.parseFormula.run()

      assert(result.isSuccess)
      assert(result.get == expected)
    }
  }

  it should "reject invalid inputs" in {
    val invalid = List(
      "(emp",
      "emp = a",
      "emp = emp",
      "a -> <a)",
      "a = b -* emp",
      "~emp"
    )

    for (input <- invalid) {
      val parser = new GslParser(input)
      val result = parser.parseFormula.run()

      assert(result.isFailure)
    }
  }
}
