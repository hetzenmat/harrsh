package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.GSL.SID.SID
import at.forsyte.harrsh.GSL.SID.SID.Rule
import at.forsyte.harrsh.GSL.projections.prototype.{StackForestProjection, TreeProjection}
import at.forsyte.harrsh.GSL.query.QueryContext
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}
import org.scalatest.PrivateMethodTester
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet

class StackForestProjectionTest extends AnyFlatSpec with PrivateMethodTester {

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

  def setSID(sid: SID): Unit = {
    val setSID = PrivateMethod[Unit](Symbol("setSID"))

    QueryContext.invokePrivate(setSID(SIDs.toBtw(sid)))
  }

  "StackForestProjection" should "correctly compute all rescopings and composition for Example 7.33 (first part)" in {
    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    setSID(SIDs.ls)
    val left = new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("ls")(x2, x3)), P("ls")(x1, x3))))
    val right = new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), P("ls")(x2, x3))))

    assert(StackForestProjection.composition(left, right).contains(new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), P("ls")(x1, x3))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.33 (second part)" in {
    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    setSID(SIDs.ls)
    val left = new StackForestProjection(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x2, _1)), P("ls")(x1, _1))))
    val right = new StackForestProjection(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x2, _1))))

    assert(StackForestProjection.composition(left, right).contains(new StackForestProjection(SortedSet(), SortedSet(_1), Seq(TreeProjection(Seq(P("ls")(x3, _1)), P("ls")(x1, _1))))))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (first part)" in {
    setSID(SIDs.lseg)
    val left = new StackForestProjection(SortedSet(_1),
                                         SortedSet(),
                                         Seq(TreeProjection(Seq(P("lseg")(y, _1)), P("cyclic")(x, y, z)),
                                             TreeProjection(Seq(), P("lseg")(z, _1))).sorted)

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          Seq(TreeProjection(Seq(P("lseg")(z, _1)), P("lseg")(y, _1))))

    val result = new StackForestProjection(SortedSet(_1),
                                           SortedSet(),
                                           (left.formula ++ right.formula).sorted)

    val allRescopings = StackForestProjection.allRescopings(left, right)
    assert(allRescopings.contains(result))

    assert(allRescopings.flatMap(_.derivableSet).exists(_.formula == Seq(TreeProjection(Seq(), P("cyclic")(x, y, z)))))

    assert(StackForestProjection.composition(left, right).exists(_.formula == Seq(TreeProjection(Seq(), P("cyclic")(x, y, z)))))
  }

  it should "correctly compute composition of Example 10.30 in 'Dissertation Pagel'" in {
    val (x1, x2, x3): (FreeVar, FreeVar, FreeVar) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    setSID(SID.buildSID(Seq.empty))

    val p1 = P("p1")(x1, x2, x3)
    val p2 = P("p2")(x3, x2, _1)
    val ptr = P("ptr")(x2, _1)

    val sf1 = new StackForestProjection(SortedSet(_1), SortedSet(),
                                        Seq(TreeProjection(Seq(p2), p1),
                                            TreeProjection(Seq(), ptr)).sorted)
    val sf2 = new StackForestProjection(SortedSet(), SortedSet(_1),
                                        Seq(TreeProjection(Seq(ptr), p2)))

    val result = new StackForestProjection(SortedSet(),
                                           SortedSet(),
                                           Seq(TreeProjection(Seq(), p1)))

    assert(StackForestProjection.composition(sf1, sf2).contains(result))
  }

  it should "correctly compute all rescopings and composition for Example 7.34 (second part)" in {
    val tll_abc = P("tll")(a, b, c)
    val tll_xyz = P("tll")(x, y, z)
    val ptr_bc = P("ptr3")(b, nil, nil, c)
    val ptr_cr = P("ptr3")(c, nil, nil, _1)

    setSID(SID.buildSID(Seq.empty))

    val left = new StackForestProjection(SortedSet(_1),
                                         SortedSet(),
                                         Seq(TreeProjection(Seq(tll_abc), tll_xyz),
                                             TreeProjection(Seq(), ptr_bc),
                                             TreeProjection(Seq(), ptr_cr)).sorted)

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          Seq(TreeProjection(Seq(ptr_bc, ptr_cr), tll_abc)))

    val result = new StackForestProjection(SortedSet(_1),
                                           SortedSet(),
                                           (left.formula ++ right.formula).sorted)

    assert(StackForestProjection.allRescopings(left, right).contains(result))

    assert(StackForestProjection.composition(left, right).contains(new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(), tll_xyz)))))
  }

  it should "correctly compute all the composition for Example 7.36" in {

    val (x1, x2, x3) = (FreeVar("x1"), FreeVar("x2"), FreeVar("x3"))

    setSID(SID.buildSID(Seq.empty))

    val left = new StackForestProjection(SortedSet(),
                                         SortedSet(_1),
                                         Seq(TreeProjection(Seq(P("even")(x2, _1)), P("odd")(x1, _1))))

    val right = new StackForestProjection(SortedSet(),
                                          SortedSet(_1),
                                          Seq(TreeProjection(Seq(P("odd")(x3, _1)), P("even")(x2, _1))))

    val result = new StackForestProjection(SortedSet(),
                                           SortedSet(_1),
                                           Seq(TreeProjection(Seq(P("odd")(x3, _1)), P("odd")(x1, _1))))

    assert(StackForestProjection.composition(left, right).contains(result))
  }

  it should "correctly compute if a projection is delimited" in {
    setSID(SID.buildSID(Seq(Rule("my_ptr", Seq("a", "b"), SymbolicHeap.buildSymbolicHeap(Seq(), Seq(Atom.PointsTo(FreeVar("a"), Seq(FreeVar("b")))))))))

    val sfp1 = new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("my_ptr")(a, b)), P("my_ptr")(b, c))))

    assert(sfp1.isDelimited())

    val sfp2 = new StackForestProjection(SortedSet(), SortedSet(), Seq(TreeProjection(Seq(P("my_ptr")(a, b), P("my_ptr")(a, c)), P("my_ptr")(b, c))))

    assert(!sfp2.isDelimited())

    val sfp3 = new StackForestProjection(SortedSet(_1), SortedSet(), Seq(TreeProjection(Seq(P("my_ptr")(_1, b), P("my_ptr")(a, c)), P("my_ptr")(b, c))))

    assert(!sfp3.isDelimited())
  }
}
