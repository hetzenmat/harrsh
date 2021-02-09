package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.Predicate
import at.forsyte.harrsh.parsers.GslParser
import at.forsyte.harrsh.seplog.FreeVar
import org.scalatest.flatspec.AnyFlatSpec

class SlBtwTest extends AnyFlatSpec {
  "Predicate" should "correctly compute progress and establishment for lseg" in {
    val parser = new GslParser(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (x2) * lseg(y, x2)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("lseg"))

    val pred: Predicate = sid.predicates("lseg")

    assert(pred.predroot == 0)
    assert(pred.bodies.forall(_.lref == Set(FreeVar("x2"))))

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesEstablishment)
  }

  "SID" should "correctly compute progress and establishment for odd/even" in {
    val parser = new GslParser(
      """
        |odd(x1,x2) <= x1 -> x2
        |odd(x1, x2) <= ∃y. x1 -> y * even(y, x2)
        |even(x1,x2) <= ∃y.x1 -> (y) * odd(y, x2)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("odd", "even"))

    val odd: Predicate = sid.predicates("odd")
    val even: Predicate = sid.predicates("even")

    assert(odd.predroot == 0)
    assert(even.predroot == 0)

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesEstablishment)
  }

  it should "determine that lists with dangling pointers are not established" in {
    val parser = new GslParser(
      """
        |llextra(x) <= x -> <nil, nil>
        |llextra(x) <= ∃n e. x -> (n, e) * llextra(n)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)
    assert(!result.get.satisfiesEstablishment)

    val parser2 = new GslParser(
      """
        |ls(x) <= ∃y. x -> y
        |""".stripMargin)
    val result2 = parser2.parseSID.run()

    assert(result2.isSuccess)
    assert(!result2.get.satisfiesEstablishment)
  }

  it should "correctly compute progress and establishment for tll" in {
    val parser = new GslParser(
      """
        |tll(x1, x2, x3) <= (x1 -> <null, null, x3>) * (x1 = x2)
        |tll(x1, x2, x3) <= ∃l r m. (x1 -> <l, r, null>) * tll(l, x2, m) * tll(r, m, x3)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("tll"))

    val tll: Predicate = sid.predicates("tll")

    assert(tll.predroot == 0)

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesEstablishment)
  }
}
