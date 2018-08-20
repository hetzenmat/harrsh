package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.refinement.RefinementAlgorithms
import at.forsyte.harrsh.seplog.FreeVar
import at.forsyte.harrsh.seplog.inductive.{PredCall, SID, SymbolicHeap}
import at.forsyte.harrsh.test.HarrshTableTest
import at.forsyte.harrsh.{ExampleSIDs, TestValues}

class EntailmentAutomatonTest extends HarrshTableTest with TestValues {

  import EntailmentAutomatonTest._

  property("List entailment") {

    val nel = ExampleSIDs.Nel
    val rhs = P("nel")(x1,x2)
    val sinlgePtrLhs = SID.fromSymbolicHeap(SymbolicHeap(x1 -> x2))
    val reversedSinlgePtrLhs = SID.fromSymbolicHeap(SymbolicHeap(x2 -> x1))
    val twoPtrLhs = SID("twoptrs",
      "List of length 2",
      Map("twoptrs" -> x1),
      // twoptrs <= emp : { a = b }
      ("oneptr", Seq.empty, SymbolicHeap(x1 -> x2)),
      // twoptrs <= ∃ y . a -> y * twoptrs(y, b)
      ("twoptrs", Seq("y"), SymbolicHeap(x1 -> y1, P("oneptr")(y1, x2)))
    )

    val sllTable = Table(
      ("lhsSid", "rhsSid", "rhsCall", "shouldHold"),
      //(sinlgePtrLhs, nel, P("nel")(x1,x2), EntailmentHolds),
      //(sinlgePtrLhs, nel, P("nel")(FreeVar("z1"),FreeVar("z2")), EntailmentFails),
      (reversedSinlgePtrLhs, nel, P("nel")(x1,x2), EntailmentFails),
      (reversedSinlgePtrLhs, nel, P("nel")(x2,x1), EntailmentHolds)
      //(twoPtrLhs, nel, P("nel")(x1,x2), EntailmentHolds)
    )

    forAll(sllTable) {
      (lhsSid, rhsSid, rhsCall, shouldHold) =>
        Given(s"LHS $lhsSid and RHS $rhsCall w.r.t. RHS-SID $rhsSid")
        Then(s"Entailment should hold: $shouldHold")

        val (aut, reach) = refine(rhsSid, rhsCall, lhsSid)
        info("Refinement result: " + serializeResult(aut, reach))
        verifyEntailment(aut, lhsSid.startPred, reach) shouldEqual shouldHold
    }

  }

}

object EntailmentAutomatonTest extends TestValues {

  val EntailmentFails = false
  val EntailmentHolds = true

  def main(args: Array[String]): Unit = {

    // Entailment check: x1 -> x2 |= nel(x1, x2)
    val nel = ExampleSIDs.Nel
    val rhs = P("nel")(x1,x2)
    val lhs = SID.fromSymbolicHeap(SymbolicHeap(x1 -> x2))

    val (lhsSid, rhsSid, rhsCall, shouldHold) = (lhs, nel, rhs, EntailmentHolds)

    println(s"Success: " + (check(rhsSid, rhsCall, lhsSid) == shouldHold))
  }

  def refine(sid: SID, rhs: PredCall, lhs: SID): (EntailmentAutomaton, Set[(String, EntailmentAutomaton.State)]) = {
    val aut = new EntailmentAutomaton(sid, rhs)
    val reachable: Set[(String, EntailmentAutomaton.State)] = RefinementAlgorithms.allReachableStates(lhs, aut, reportProgress = true)
    (aut, reachable)
  }

  def verifyEntailment(aut: EntailmentAutomaton, lhsTopLevelPred: String, reachable: Set[(String, EntailmentAutomaton.State)]) = {
    val isFinal = (s: EntailmentAutomaton.State) => aut.isFinal(s)
    if (reachable.forall{
      case (pred, _) => pred != lhsTopLevelPred
    }) throw new IllegalArgumentException(s"Malformed test case: LHS start predicate ${lhsTopLevelPred} unreachable, so entailment trivially holds")
    val entailmentHolds = reachable.forall{
      case (pred, state) => pred != lhsTopLevelPred || isFinal(state)
    }
    entailmentHolds
  }

  def check(sid: SID, rhs: PredCall, lhs: SID): Boolean = {
    println(s"Checking ${lhs.callToStartPred} |= $rhs for SID '${sid.description}'")
    val (aut, reachable) = refine(sid, rhs, lhs)
    println(serializeResult(aut, reachable))
    verifyEntailment(aut, lhs.startPred, reachable)
  }

  private def indent(s : String) = "  " + s

  def serializeResult(aut: EntailmentAutomaton, reachable: Set[(String, EntailmentAutomaton.State)]): String = {
    val isFinal = (s: EntailmentAutomaton.State) => aut.isFinal(s)
    serializeReach(reachable, isFinal)
  }

  def serializeReach(states: Set[(String, EntailmentAutomaton.State)], isFinal: EntailmentAutomaton.State => Boolean): String = {
    val statesByPred: Map[String, Set[EntailmentAutomaton.State]] = states.groupBy(_._1).mapValues(pairs => pairs.map(_._2))
    val lines = Stream("RESULT {") ++ statesByPred.toStream.flatMap(pair => serializePred(pair._1, pair._2, isFinal)).map(indent) ++ Stream("}")
    lines.mkString("\n")
  }

  def serializePred(pred: String, states: Set[EntailmentAutomaton.State], isFinal: EntailmentAutomaton.State => Boolean): Stream[String] = {
    Stream(s"PRED $pred {") ++ states.toStream.flatMap(s => serializeState(s, isFinal)).map(indent) ++ Stream("}")
  }

  def serializeState(state: EntailmentAutomaton.State, isFinal: EntailmentAutomaton.State => Boolean): Stream[String] = {
    (Stream("STATE {",
      s"  PARAMS: ${state.orderedParams.mkString(", ")}")
      ++ Some("  FINAL").filter(_ => isFinal(state))
    ++ state.ets.toStream.flatMap(serializeET).map(indent) ++ Stream("}"))
  }

  def serializeET(et: ExtensionType): Stream[String] = {
    et.toString.lines.toStream
  }

}
