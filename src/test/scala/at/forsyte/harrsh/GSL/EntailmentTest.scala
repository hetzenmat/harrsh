package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.parsers.GslParser
import org.scalatest.Assertions.fail
import org.scalatest.flatspec.AnyFlatSpec

import scala.util.{Failure, Success}

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

  val lseg_ls: SID = get(
    """
      |lseg(x1,x2) <= x1 -> <x2>
      |lseg(x1,x2) <= ∃y.x1 -> (y) * lseg(y, x2)
      |ls(x1) <= x1 -> nil
      |ls(x1) <= ∃y.x1 -> (y) * ls(y)
      |""".stripMargin)

  val ptr1: SID = get(
    """
      |ptr1(x1,x2) <= x1 -> x2
      |""".stripMargin)

  def toBtw(s: SID): SID_btw = s.toBtw match {
    case Left(value) => fail(value)
    case Right(value) => value
  }
}

class EntailmentTest extends AnyFlatSpec {

  implicit class StringImprovements(val s: String) {

    def |=(other: String): GslFormula = Negation(parseFormula(s), parseFormula(other))
  }

  def parseFormula(s: String): GslFormula = {
    new GslParser(s).parseFormula.run() match {
      case Failure(f) =>
        println(f)
        fail(f)
      case Success(formula) => formula
    }
  }


  "Type computation" should "correctly decide entailments (lseg) (Does not yet work)" in {
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