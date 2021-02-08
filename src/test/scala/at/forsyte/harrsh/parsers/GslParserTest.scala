package at.forsyte.harrsh.parsers

import at.forsyte.harrsh.GSL.GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula._
import at.forsyte.harrsh.GSL.SymbolicHeap
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst}
import org.scalatest.flatspec.AnyFlatSpec

class GslParserTest extends AnyFlatSpec {

  val _1: BoundVar = BoundVar(1)
  val _2: BoundVar = BoundVar(2)
  val _3: BoundVar = BoundVar(3)

  val a: FreeVar = FreeVar("a")
  val b: FreeVar = FreeVar("b")
  val c: FreeVar = FreeVar("c")

  "GSL parser" should "accept well-formed GSL formulae" in {
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

  it should "reject ill-formed GSL formulae" in {
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

  it should "accept well-formed symbolic heaps" in {
    val valid = List(
      ("∃a b c. a = b * c -> <a, b> * call(a, b)", SymbolicHeap(3, Vector(PointsTo(_3, Vector(_1, _2))), Vector(PredicateCall("call", Vector(_1, _2))), Vector(Equality(_1, _2)), Seq())),
      ("∃ aaa. aaa = a", SymbolicHeap(1, Seq(), Seq(), Seq(Equality(_1, FreeVar("a"))), Seq())),
      ("a != b * test (  c)", SymbolicHeap(0, Seq(), Seq(PredicateCall("test", Seq(c))), Seq(), Seq(DisEquality(a, b))))
    )

    for ((input, expected) <- valid) {
      val parser = new GslParser(input)
      val result = parser.parseSymbolicHeap.run()

      assert(result.isSuccess)
      assert(result.get == expected)
    }
  }

  it should "reject ill-formed symbolic heaps" in {
    val invalid = List(
      "∃ a = b",
      "∃ a. a",
      "∃ a a = b",
      "call(acb,)",
      "a = b * ∃ a . a = b"
    )

    for (input <- invalid) {
      val parser = new GslParser(input)
      val result = parser.parseSymbolicHeap.run()

      assert(result.isFailure)
    }
  }
}
