package at.forsyte.harrsh.modelchecking

import at.forsyte.harrsh.pure.EqualityUtils
import at.forsyte.harrsh.seplog.{FreeVar, Var}
import at.forsyte.harrsh.seplog.inductive.{AtomContainer, SymbolicHeap}
import at.forsyte.harrsh.test.HarrshTableTest
import at.forsyte.harrsh.{Implicits, TestValues}

/**
  * Created by jens on 2/24/17.
  */
class ModelToFormulaTest extends HarrshTableTest with Implicits with TestValues {

  // TODO Add test cases violating the assertions

  val testCases = Table(
    ("stack", "heap", "result"),
    // Simple model with pairwise different variables, all of which are non-null
    (Map(x1 -> 5, x2 -> 42, x3 -> 55),
      Map(5 -> Seq(42, 55), 42 -> Seq(55), 55 -> Seq(3), 3 -> Seq(0)),
      "∃y1 . x1 ↦ (x2, x3) * x2 ↦ x3 * x3 ↦ y1 * y1 ↦ null".parse),

    // Stack with some null vars
      (Map(x1 -> 5, x2 -> 42, x3 -> 0, x4 -> 0),
       Map(5 -> Seq(42, 55), 42 -> Seq(55), 55 -> Seq(3), 3 -> Seq(0)),
        "∃y1 ∃y2 . x1 ↦ (x2, y1) * x2 ↦ y1 * y1 ↦ y2 * y2 ↦ null : {x3 ≈ x4, x3 ≈ null, x4 ≈ null}".parse),

    // Additionally multiple equal vars
    (Map(x1 -> 5, x2 -> 42, x3 -> 0, x4 -> 0, x5 -> 42, x6 -> 42),
      Map(5 -> Seq(42, 55), 42 -> Seq(55), 55 -> Seq(3), 3 -> Seq(0)),
      "∃y1 ∃y2 . x1 ↦ (x2, y1) * x2 ↦ y1 * y1 ↦ y2 * y2 ↦ null : {x2 ≈ x5, x5 ≈ x6, x3 ≈ x4, x3 ≈ null, x4 ≈ null}".parse),

    //Stack with multiple bound vars
    (Map(x1 -> 5, x2 -> 42, x3 -> 0),
      Map(5 -> Seq(42, 55), 42 -> Seq(55), 55 -> Seq(3,8), 3 -> Seq(0), 8 -> Seq(19, 22), 19 -> Seq(0), 22 -> Seq(0)),
      "∃y1 ∃y2 ∃y3 ∃y4 ∃y5 . x1 ↦ (x2, y1) * x2 ↦ y1 * y2 ↦ null * y3 ↦ null * y1 ↦ (y3, y4) * y4 ↦ (y5, y2) * y5 ↦ null : {x3 ≈ null}".parse)
  )

  property("The conversion of models to symbolic heaps") {
    forAll(testCases) {
      (stack : Map[FreeVar,Loc], heap : Map[Loc,Seq[Loc]], expectedRes : SymbolicHeap) =>
        val res = ModelToFormula(Model(stack.map(p => (p._1.asInstanceOf[Var], p._2)), heap))
        info("Model-to-formula conversion result " + res + " should equal " + expectedRes)
        // Mapping onto the atoms to be agnostic about free-variable order
        val AtomContainer(resPure, resPointers, resPredCalls) = res.atoms
        val AtomContainer(expPure, expPointers, expPredCalls) = expectedRes.atoms

        resPure.map(EqualityUtils.orderedAtom).toSet shouldEqual expPure.map(EqualityUtils.orderedAtom).toSet
        resPointers.toSet shouldEqual expPointers.toSet
        resPredCalls.toSet shouldEqual expPredCalls.toSet

        // res.atoms shouldEqual expectedRes.atoms
    }
  }

}
