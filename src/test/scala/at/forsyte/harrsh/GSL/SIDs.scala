package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.parsers.GslParser
import org.scalatest.Assertions.fail

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

  val even_odd: SID = get(
    """
      |odd(x1, x2) <= x1 -> (x2)
      |odd(x1, x2) <= ∃a. x1 -> <a> * even(a, x2)
      |even(x1, x2) <= ∃b. x1 -> b * odd(b, x2)
      |""".stripMargin)

  val btree: SID = get(
    """
      |btree(x1) <= x1 -> <null, null>
      |btree(x1) <= ∃ l r. x1 -> <l, r> * btree(l) * btree(r)
      |""".stripMargin
    )

  val ptr1: SID = get(
    """
      |ptr1(x1,x2) <= x1 -> x2
      |""".stripMargin)

  val ptr2: SID = get(
    """
      |ptr2(x1,x2, x3) <= x1 -> (x2, x3)
      |""".stripMargin)

  def toBtw(s: SID): SID_btw = s.toBtw match {
    case Left(value) => fail(value)
    case Right(value) => value
  }

  def parseFormula(s: String): GslFormula = {
    new GslParser(s).parseFormula.run() match {
      case Failure(f) =>
        println(f)
        fail(f)
      case Success(formula) => formula
    }
  }

  implicit class StringImprovements(val s: String) {

    def |=(other: String): GslFormula = Negation(parseFormula(s), parseFormula(other))
  }
}

