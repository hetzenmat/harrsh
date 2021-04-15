package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.GSL.SID.SID.Rule
import at.forsyte.harrsh.GSL.projections.{StackForestProjection, TreeProjection}
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

    val left = new StackForestProjection(SortedSet(), SortedSet(), SortedSet(TreeProjection(Seq(P("ls")(x2, x3)), P("ls")(x1, x3))))
    val right = new StackForestProjection(SortedSet(), SortedSet(), SortedSet(projections.TreeProjection(Seq(), P("ls")(x2, x3))))

    assert(StackForestProjection.composition(left, right, SIDs.toBtw(SIDs.ls)).contains(new StackForestProjection(SortedSet(), SortedSet(), SortedSet(projections.TreeProjection(Seq(), P("ls")(x1, x3))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.33 (second part)" in {
    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    val left = new StackForestProjection(SortedSet(), SortedSet(_1), SortedSet(projections.TreeProjection(Seq(P("ls")(x2, _1)), P("ls")(x1, _1))))
    val right = new StackForestProjection(SortedSet(), SortedSet(_1), SortedSet(projections.TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x2, _1))))

    assert(StackForestProjection.composition(left, right, SIDs.toBtw(SIDs.ls)).contains(new StackForestProjection(SortedSet(), SortedSet(_1), SortedSet(projections.TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x1, _1))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (first part)" in {

    val left = new StackForestProjection(SortedSet(_1),
                                         SortedSet(),
                                         SortedSet(projections.TreeProjection(Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
                                                   projections.TreeProjection(Seq(), P("lseg")(z, _1))))

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          SortedSet(projections.TreeProjection(Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    val result = new StackForestProjection(SortedSet(_1),
                                           SortedSet(),
                                           left.formula ++ right.formula)

    val allRescopings = StackForestProjection.allRescopings(left, right)
    assert(allRescopings.contains(result))

    assert(allRescopings.flatMap(_.derivableSet).exists(_.formula == SortedSet(projections.TreeProjection(Seq(), P("cyclic")(x, y, z)))))

    assert(StackForestProjection.composition(left, right, SIDs.toBtw(SIDs.lseg)).exists(_.formula == SortedSet(projections.TreeProjection(Seq(), P("cyclic")(x, y, z)))))
  }

  it should "correctly compute composition of Example 10.30 in 'Dissertation Pagel'" in {
    val (x1, x2, x3): (FreeVar, FreeVar, FreeVar) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    val p1 = P("p1")(x1, x2, x3)
    val p2 = P("p2")(x3, x2, _1)
    val ptr = P("ptr")(x2, _1)

    val sf1 = new StackForestProjection(SortedSet(_1), SortedSet(),
                                        SortedSet(projections.TreeProjection(Seq(p2), p1),
                                                  projections.TreeProjection(Seq(), ptr)))
    val sf2 = new StackForestProjection(SortedSet(), SortedSet(_1),
                                        SortedSet(projections.TreeProjection(Seq(ptr), p2)))

    val result = new StackForestProjection(SortedSet(),
                                           SortedSet(),
                                           SortedSet(projections.TreeProjection(Seq(), p1)))

    assert(StackForestProjection.composition(sf1, sf2, SIDs.toBtw(SID.SID.buildSID(Seq.empty))).contains(result))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (second part)" in {
    val tll_abc = P("tll")(a, b, c)
    val tll_xyz = P("tll")(x, y, z)
    val ptr_bc = P("ptr3")(b, nil, nil, c)
    val ptr_cr = P("ptr3")(c, nil, nil, _1)

    val left = new StackForestProjection(SortedSet(_1),
                                         SortedSet(),
                                         SortedSet(projections.TreeProjection(Seq(tll_abc), tll_xyz),
                                                   projections.TreeProjection(Seq(), ptr_bc),
                                                   projections.TreeProjection(Seq(), ptr_cr)))

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          SortedSet(projections.TreeProjection(Seq(ptr_bc, ptr_cr), tll_abc)))

    val result = new StackForestProjection(SortedSet(_1),
                                           SortedSet(),
                                           left.formula ++ right.formula)

    assert(StackForestProjection.allRescopings(left, right).contains(result))

    assert(StackForestProjection.composition(left, right, SIDs.toBtw(SID.SID.buildSID(Seq.empty))).contains(new StackForestProjection(SortedSet(), SortedSet(), SortedSet(projections.TreeProjection(Seq(), tll_xyz)))))
  }

  it should "correctly compute all the composition for Example 7.36" in {

    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    val left = new StackForestProjection(SortedSet(),
                                         SortedSet(_1),
                                         SortedSet(projections.TreeProjection(Seq(P("even")(x2, _1)), P("odd")(x1, _1))))

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          SortedSet(projections.TreeProjection(Seq(P("odd")(x3, _1)), P("even")(x2, _1))))

    val result = new StackForestProjection(SortedSet(),
                                           SortedSet(_1),
                                           SortedSet(projections.TreeProjection(Seq(P("odd")(x3, _1)), P("odd")(x1, _1))))

    assert(StackForestProjection.composition(left, right, SIDs.toBtw(SID.SID.buildSID(Seq.empty))).contains(result))
  }

  it should "correctly compute if a projection is delimited" in {
    SID.SID.buildSID(Seq(Rule("my_ptr", Seq("a", "b"), SymbolicHeap.buildSymbolicHeap(Seq(), Seq(Atom.PointsTo(FreeVar("a"), Seq(FreeVar("b")))))))).toBtw match {
      case Left(_) => fail()
      case Right(sid) =>

        val sfp1 = new StackForestProjection(SortedSet(), SortedSet(), SortedSet(projections.TreeProjection(Seq(P("my_ptr")(a, b)), P("my_ptr")(b, c))))

        assert(sfp1.isDelimited(sid))

        val sfp2 = new StackForestProjection(SortedSet(), SortedSet(), SortedSet(projections.TreeProjection(Seq(P("my_ptr")(a, b), P("my_ptr")(a, c)), P("my_ptr")(b, c))))

        assert(!sfp2.isDelimited(sid))

        val sfp3 = new StackForestProjection(SortedSet(_1), SortedSet(), SortedSet(projections.TreeProjection(Seq(P("my_ptr")(_1, b), P("my_ptr")(a, c)), P("my_ptr")(b, c))))

        assert(!sfp3.isDelimited(sid))
    }
  }
}
