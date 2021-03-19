package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SIDs.parseFormula
import org.scalatest.flatspec.AnyFlatSpec

class MagicWandTest extends AnyFlatSpec {
  "Type computation" should "correctly decide magic wands" in {

    val inputs: Seq[(String, SID, Boolean)] = Seq(
      ("a -> b /\\ (ls(b) -* ls(a))", SIDs.ls, true),
      ("b -> a /\\ (ls(b) -* ls(a))", SIDs.ls, false),
      ("lseg(a, b) /\\ (lseg(b, a) -* lseg(a, a))", SIDs.lseg, true),
      ("a -> <b, c> /\\ ((btree(b) * btree(c)) -* btree(a))", SIDs.btree, true)
      )

    inputs.foreach { case (str, sid, bool) =>
      Query(parseFormula(str), sid).isSatisfiable match {
        case Left(value) => fail(value)
        case Right(value) => assert(value == bool)
      }
    }
  }
}
