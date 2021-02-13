package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.GSL.SID.Rule
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet

class StackForestProjectionTest extends AnyFlatSpec {

  def P(pred: String)(vars: Var*): PredicateCall = {
    PredicateCall(pred, vars)
  }

  val a: FreeVar = FreeVar("a")
  val b: FreeVar = FreeVar("b")
  val c: FreeVar = FreeVar("c")
  val x: FreeVar = FreeVar("x")
  val y: FreeVar = FreeVar("y")
  val z: FreeVar = FreeVar("z")
  val _1: BoundVar = BoundVar(1)
  val nil: Var = NullConst

  "StackForestProjection" should "correctly compute all rescopings and composition for Example 7.33 (first part)" in {
    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    val left = StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("ls")(x2, x3)), P("ls")(x1, x3))))
    val right = StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), P("ls")(x2, x3))))

    assert(StackForestProjection.composition(left, right).contains(StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), P("ls")(x1, x3))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.33 (second part)" in {
    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    val left = StackForestProjection.from(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x2, _1)), P("ls")(x1, _1))))
    val right = StackForestProjection.from(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x2, _1))))

    assert(StackForestProjection.composition(left, right).contains(StackForestProjection.from(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x1, _1))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (first part)" in {

    val left = StackForestProjection.from(SortedSet(_1),
                                          SortedSet(),
                                          Seq(TreeProjection(Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
                                              TreeProjection(Seq(), P("lseg")(z, _1))))

    val right = StackForestProjection.from(SortedSet(),
                                           SortedSet(_1),
                                           Seq(TreeProjection(Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    val result = StackForestProjection.from(SortedSet(_1),
                                            SortedSet(),
                                            left.formula ++ right.formula)

    val allRescopings = StackForestProjection.allRescopings(left, right)
    assert(allRescopings.contains(result))

    assert(allRescopings.flatMap(_.derivableSet).exists(_.formula == Seq(TreeProjection(Seq(), P("cyclic")(x, y, z)))))

    assert(StackForestProjection.composition(left, right).exists(_.formula == Seq(TreeProjection(Seq(), P("cyclic")(x, y, z)))))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (second part)" in {
    val tll_abc = P("tll")(a, b, c)
    val tll_xyz = P("tll")(x, y, z)
    val ptr_bc = P("ptr3")(b, nil, nil, c)
    val ptr_cr = P("ptr3")(c, nil, nil, _1)

    val left = StackForestProjection.from(SortedSet(_1),
                                          SortedSet(),
                                          Seq(TreeProjection(Seq(tll_abc), tll_xyz),
                                              TreeProjection(Seq(), ptr_bc),
                                              TreeProjection(Seq(), ptr_cr)))

    val right = StackForestProjection.from(SortedSet(),
                                           SortedSet(_1),
                                           Seq(TreeProjection(Seq(ptr_bc, ptr_cr), tll_abc)))

    val result = StackForestProjection.from(SortedSet(_1),
                                            SortedSet(),
                                            left.formula ++ right.formula)

    assert(StackForestProjection.allRescopings(left, right).contains(result))

    assert(StackForestProjection.composition(left, right).contains(StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), tll_xyz)))))
  }

  it should "correctly compute if a projection is delimited" in {
    val sid = SID(Seq(Rule("ptr1", Seq("a", "b"), SymbolicHeap.buildSymbolicHeap(Seq(), Seq(Atom.PointsTo(FreeVar("a"), Seq(FreeVar("b"))))))))

    val sfp1 = StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("ptr1")(a, b)), P("ptr1")(b, c))))

    assert(sfp1.isDelimited(sid))

    val sfp2 = StackForestProjection.from(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("ptr1")(a, b), P("ptr1")(a, c)), P("ptr1")(b, c))))

    assert(!sfp2.isDelimited(sid))

    val sfp3 = StackForestProjection.from(SortedSet(_1), SortedSet(), Seq(TreeProjection(Seq(P("ptr1")(_1, b), P("ptr1")(a, c)), P("ptr1")(b, c))))

    assert(!sfp3.isDelimited(sid))
  }
}
