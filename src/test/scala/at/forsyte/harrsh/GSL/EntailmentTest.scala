package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SIDs.{StringImprovements, parseFormula}
import org.scalatest.flatspec.AnyFlatSpec

class EntailmentTest extends AnyFlatSpec {

  "Type computation" should "correctly decide entailments (lseg)" in {
    val left = parseFormula("lseg(a, b) * lseg(b, c)")
    val right = parseFormula("lseg(a, c)")

    Query.fromEntailment(left, right, SIDs.lseg).entailmentHolds match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }
  }

  "Type computation" should "correctly decide entailments (btree)" in {
    val left = parseFormula("a -> <b, c> * b -> <null, null> * c -> (null, null)")
    val right = parseFormula("btree(a)")

    Query.fromEntailment(left, right, SIDs.btree).entailmentHolds match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }
  }



  "Type computation" should "correctly decide easy entailments" in {
    val inputs: Seq[(GslFormula, GslFormula, SID, Boolean)] = Seq({
      val left = parseFormula("a -> <b, a> * a = c")
      val right = parseFormula("c -> <b, a>")

      (left, right, SIDs.ptr2, true)
    }, {
      val left = parseFormula("a -> b * a = c")
      val right = parseFormula("c -> d")

      (left, right, SIDs.ptr1, false)
    }, {
      val left = parseFormula("a -> b /\\ a -> c")
      val right = parseFormula("a -> b * b = c")

      (left, right, SIDs.ptr1, true)
    }, {
      val left = parseFormula("a -> b /\\ a -> c")
      val right = parseFormula("a -> b")

      (left, right, SIDs.ptr1, true)
    }, {
      val left = parseFormula("a -> b /\\ a -> c")
      val right = parseFormula("a -> b * b != c")

      (left, right, SIDs.ptr1, false)
    }, {
      val left = parseFormula("a -> b * ls(b)")
      val right = parseFormula("ls(a)")

      (left, right, SIDs.ls, true)
    }, {
      val left = parseFormula("a -> b * b -> c * c -> null")
      val right = parseFormula("ls(a) /\\ (a -> b * ls(b))")

      (left, right, SIDs.ls, true)
    })

    for ((left, right, sid, expectation) <- inputs) {
      Query.fromEntailment(left, right, sid).entailmentHolds match {
        case Left(value) => fail(value)
        case Right(value) => assert(value == expectation)
      }
    }
  }

  "Type computation" should "correctly decide entailments (even/odd)" in {
    val inputs: Seq[(GslFormula, SID, Boolean)] = Seq(
//      ("a -> b" |= "odd(a, b)", SIDs.even_odd, true),
//      ("a -> b" |= "even(a, b)", SIDs.even_odd, false),
//      ("a -> b * b -> c" |= "even(a, c)", SIDs.even_odd, true),
//      ("a -> b * b -> c" |= "odd(a, c)", SIDs.even_odd, false),
//      ("odd(a, b) * b -> c" |= "even(a, c)", SIDs.even_odd, true),
//      ("odd(a, b) * b -> c" |= "odd(a, c)", SIDs.even_odd, false),
      ("odd(a, b) * even(b, c)" |= "odd(a, c)", SIDs.even_odd, true)
      )

    for ((negation, sid, expectation) <- inputs) {
      Query(negation, sid, fromEntailment = true).entailmentHolds match {
        case Left(value) => fail(value)
        case Right(value) =>
          assert(value == expectation)
      }
    }
  }

  "Type computation" should "correctly decide entailments (lseg and ls)" in {
    val inputs: Seq[(GslFormula, SID, Boolean)] = Seq(
      ("lseg(a, b) * lseg(b, a)" |= "lseg(a, a) /\\ lseg(b, b)", SIDs.lseg, true),
      ("a -> b * b -> a" |= "lseg(a, a)", SIDs.lseg, true),
      ("lseg(a, b) * b -> null" |= "ls(a)", SIDs.lseg_ls, true),
      ("lseg(a, b) * lseg(b, null)" |= "ls(a)", SIDs.lseg_ls, true),
      ("lseg(a, b) * lseg(b, null)" |= "lseg(a, null)", SIDs.lseg_ls, true),
      ("ls(a)" |= "lseg(a, null)", SIDs.lseg_ls, true),
      ("lseg(a, null)" |= "ls(a)", SIDs.lseg_ls, true),
      ("lseg(a, b)" |= "ls(a)", SIDs.lseg_ls, false),
      ("ls(a)" |= "lseg(a, b)", SIDs.lseg_ls, false),
      ("a -> b * b -> a" |= "lseg(a, b) * lseg(b, a)", SIDs.lseg, true),
      ("lseg(a, b) * lseg(b, a)" |= "a -> b * b -> a", SIDs.lseg, false)
      )

    for ((negation, sid, expectation) <- inputs) {
      Query(negation, sid, fromEntailment = true).entailmentHolds match {
        case Left(value) => fail(value)
        case Right(value) =>
          assert(value == expectation)
      }
    }
  }
}