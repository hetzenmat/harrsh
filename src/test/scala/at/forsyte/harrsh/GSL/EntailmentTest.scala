package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.parsers.GslParser
import org.scalatest.flatspec.AnyFlatSpec

import scala.util.{Failure, Success}

class EntailmentTest extends AnyFlatSpec {

  object SIDs {
    private def get(s: String): SID = {
      new GslParser(s).parseSID.run() match {
        case Failure(f) =>
          println(f)
          fail()

        case Success(sid) => sid
      }
    }

    val lseg: SID = get(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (y) * lseg(y, x2)
        |""".stripMargin)

    val ls: SID = get(
      """
        |ls(x1) <= x1 -> nil
        |ls(x1) <= ∃y.x1 -> (y) * ls(y)
        |""".stripMargin)

    val ptr1: SID = get(
      """
        |ptr1(x1,x2) <= x1 -> x2
        |""".stripMargin)
  }

  def parseFormula(s: String): GslFormula = {
    new GslParser(s).parseFormula.run() match {
      case Failure(f) =>
        println(f)
        fail(f)
      case Success(formula) => formula
    }
  }

  def toBtw(s: SID): SID_btw = s.toBtw match {
    case Left(value) => fail(value)
    case Right(value) => value
  }

  "Type computation" should "correctly decide entailments (lseg)" in {
    val left = parseFormula("lseg(a, b) * lseg(b, c)")
    val right = parseFormula("lseg(a, c)")

    Query.fromEntailment(left, right, SIDs.lseg).entailmentHolds match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }
  }

  "Type computation" should "correctly decide easy entailments" in {
    val inputs: Seq[(GslFormula, GslFormula, SID, Boolean)] = Seq({
      val left = parseFormula("a -> b * a = c")
      val right = parseFormula("c -> b")

      (left, right, SIDs.ptr1, true)
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
    })

    for ((left, right, sid, expectation) <- inputs) {
      Query.fromEntailment(left, right, sid).entailmentHolds match {
        case Left(value) => fail(value)
        case Right(value) => assert(value == expectation)
      }
    }
  }

  "Type computation" should "correctly decide entailments (lseg and ls)" in {
    val left = parseFormula("lseg(a, b) * b -> null")
    val right = parseFormula("ls(a)")

    Query.fromEntailment(left, right, SIDs.lseg).entailmentHolds match {
      case Left(value) => fail(value)
      case Right(value) => assert(value)
    }
  }
}