package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Negation
import at.forsyte.harrsh.parsers.GslParser
import org.scalatest.flatspec.AnyFlatSpec

import scala.util.{Failure, Success}

class EntailmentTest extends AnyFlatSpec {

  object SIDs {
    private def get(s: String): SID = {
      new GslParser(s).parseSID.run() match {
        case Failure(f) => { println(f); fail() }
        case Success(sid) => sid
      }
    }

    val lseg: SID = get(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (y) * lseg(y, x2)
        |""".stripMargin)

  }

  def parseFormula(s: String): GslFormula = {
    new GslParser(s).parseFormula.run() match {
      case Failure(_) => fail()
      case Success(formula) => formula
    }
  }

  "Type computation" should "correctly decide entailments" in {
    val left = parseFormula("lseg(a, b) * lseg(b, c)")
    val right = parseFormula("lseg(a, d)")

    val q = Query(Negation(left, right), SIDs.lseg, fromEntailment = true)

    println(q.isSatisfiable)
  }
}
