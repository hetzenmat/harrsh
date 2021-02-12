package at.forsyte.harrsh.GSL

import org.scalatest.flatspec.AnyFlatSpec

class UtilsTest extends AnyFlatSpec {
  "Utils" should "correctly compare sequences lexicographically" in {
    assert(Utils.compareLexicographically(Seq(1, 10), Seq(2)) < 0)
    assert(Utils.compareLexicographically(Seq(2, 10), Seq(2)) > 0)
    assert(Utils.compareLexicographically(Seq(2, 10), Seq(2, 10)) == 0)
    assert(Utils.compareLexicographically(Seq(), Seq(2, 10)) < 0)
  }
}
