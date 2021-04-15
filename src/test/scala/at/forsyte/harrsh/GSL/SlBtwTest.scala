package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.SID
import at.forsyte.harrsh.GSL.SID.SID.Predicate
import at.forsyte.harrsh.parsers.GslParser
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar}
import org.scalatest.flatspec.AnyFlatSpec

class SlBtwTest extends AnyFlatSpec {
  "Predicate" should "correctly compute progress, connectivity and establishment for lseg" in {
    val parser = new GslParser(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (y) * lseg(y, x2)
        |""".stripMargin)
    val result = parser.parseSID.run()


    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("lseg"))

    val pred: Predicate[SymbolicHeap] = sid.predicates("lseg")

    assert(pred.predrootIndex == 0)
    assert(pred.rules.head.lref == Set(FreeVar("x2")))
    assert(pred.rules.tail.head.lref == Set(BoundVar(1)))

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesConnectivity)
    assert(sid.satisfiesEstablishment)

    sid.toBtw match {
      case Left(_) => fail()
      case Right(s) => assert(s != null)
    }
  }

  "SID" should "correctly compute progress, connectivity and establishment for odd/even" in {
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

    val odd: Predicate[SymbolicHeap] = sid.predicates("odd")
    val even: Predicate[SymbolicHeap] = sid.predicates("even")

    assert(odd.predrootIndex == 0)
    assert(even.predrootIndex == 0)

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesConnectivity)
    assert(sid.satisfiesEstablishment)

    assert(sid.toBtw.isRight)
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
    assert(result.get.toBtw.isLeft)

    val parser2 = new GslParser(
      """
        |ls(x) <= ∃y. x -> y
        |""".stripMargin)
    val result2 = parser2.parseSID.run()

    assert(result2.isSuccess)
    assert(result2.get.satisfiesConnectivity)
    assert(!result2.get.satisfiesEstablishment)

    assert(result2.get.toBtw.isLeft)
  }

  it should "correctly compute progress, connectivity and establishment for tll" in {
    val parser = new GslParser(
      """
        |tll(x1, x2, x3) <= (x1 -> <null, null, x3>) * (x1 = x2)
        |tll(x1, x2, x3) <= ∃l r m. (x1 -> <l, r, null>) * tll(l, x2, m) * tll(r, m, x3)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("tll"))

    val tll: Predicate[SymbolicHeap] = sid.predicates("tll")

    assert(tll.predrootIndex == 0)

    assert(sid.satisfiesProgress)
    assert(sid.satisfiesConnectivity)
    assert(sid.satisfiesEstablishment)

    assert(sid.toBtw.isRight)
  }

  it should "correctly determine that a variant of lseg does not satisfy connectivity" in {
    val parser = new GslParser(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (x2) * lseg(y, x2)
        |""".stripMargin)
    val result = parser.parseSID.run()

    assert(result.isSuccess)

    val sid: SID = result.get

    assert(sid.predicates.keySet == Set("lseg"))

    val pred: Predicate[SymbolicHeap] = sid.predicates("lseg")

    assert(pred.predrootIndex == 0)
    assert(pred.rules.head.lref == Set(FreeVar("x2")))
    assert(pred.rules.tail.head.lref == Set(FreeVar("x2")))

    assert(sid.satisfiesProgress)
    assert(!sid.satisfiesConnectivity)
    assert(sid.satisfiesEstablishment)

    assert(sid.toBtw.isLeft)
  }
}
