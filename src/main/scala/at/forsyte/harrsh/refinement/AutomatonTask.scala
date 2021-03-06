package at.forsyte.harrsh.refinement

import at.forsyte.harrsh.heapautomata._
import at.forsyte.harrsh.heapautomata.instances.{ToyExampleAutomata, TrackingAutomata}
import at.forsyte.harrsh.seplog.Var
import at.forsyte.harrsh.seplog.inductive.PureAtom
import at.forsyte.harrsh.util.Combinators

/**
  * Created by jkatelaa on 10/20/16.
  */
sealed trait AutomatonTask {

  // FIXME Allow null as target in reachability
  // TODO Possibly give Boolean param to SAT, EST etc instead of having two separate case classes?

  def getAutomaton : HeapAutomaton = this match {
    case RunHasPointer(negate : Boolean) => ToyExampleAutomata.hasPointerAutomaton(negate)
    case RunModulo(remainder : Int, divisor : Int, negate : Boolean) => ToyExampleAutomata.moduloAutomaton(remainder, divisor, negate)
    case RunExactTracking(alloc, pure, negate) => TrackingAutomata.singleTargetStateTracking(alloc, pure, negate)
    case RunRelaxedTracking(alloc, pure, negate) => TrackingAutomata.subsetTracking(alloc, pure, negate)
    case RunAllocationTracking(alloc, negate) => TrackingAutomata.allocTracking(alloc, negate)
    case RunPureTracking(pure, negate) => TrackingAutomata.pureTracking(pure, negate)
    case RunSat => TrackingAutomata.satAutomaton
    case RunUnsat => TrackingAutomata.unsatAutomaton
    case RunEstablishment => TrackingAutomata.establishmentAutomaton
    case RunNonEstablishment => TrackingAutomata.nonEstablishmentAutomaton
    case RunReachability(from, to, negate) => TrackingAutomata.reachabilityAutomaton(from, to, negate)
    case RunGarbageFreedom => TrackingAutomata.garbageFreedomAutomaton
    case RunWeakAcyclicity => TrackingAutomata.weakAcyclicityAutomaton
    case RunMayHaveGarbage => TrackingAutomata.mayHaveGarbageAutomaton
    case RunStrongCyclicity => TrackingAutomata.strongCyclicityAutomaton
  }

  // TODO Finish complementation
  def complement : AutomatonTask = this match {
    case RunHasPointer(negate : Boolean) => RunHasPointer(!negate)
    case RunModulo(remainder, divisor, negate : Boolean) =>
      if (divisor == 2) RunModulo(1-remainder, divisor, negate) else RunModulo(remainder, divisor, !negate)
    case RunAllocationTracking(alloc, negate) => RunAllocationTracking(alloc, !negate)
    case RunPureTracking(pure, negate) => RunPureTracking(pure, !negate)
    case RunExactTracking(alloc, pure, negate) => RunExactTracking(alloc, pure, !negate)
    case RunRelaxedTracking(alloc, pure, negate) => RunRelaxedTracking(alloc, pure, !negate)
    case RunSat => RunUnsat
    case RunUnsat => RunSat
    case RunEstablishment => RunNonEstablishment
    case RunNonEstablishment => RunEstablishment
    case RunReachability(from, to, negate) => RunReachability(from, to, !negate)
    case RunGarbageFreedom => RunMayHaveGarbage
    case RunWeakAcyclicity => RunStrongCyclicity
    case RunMayHaveGarbage => RunGarbageFreedom
    case RunStrongCyclicity => RunWeakAcyclicity
  }

  private def negationPrefix(negate : Boolean) = if (negate) "~" else ""

  override def toString: String = this match {
    case RunHasPointer(negate : Boolean) => negationPrefix(negate) + AutomatonTask.keywords.hasptr
    case RunModulo(remainder : Int, divisor : Int, negate : Boolean) => (remainder, divisor, negate) match {
      case (1, 2, false) => AutomatonTask.keywords.odd
      case (0, 2, false) => AutomatonTask.keywords.even
      case _ => negationPrefix(negate) + AutomatonTask.keywords.mod + "[" + remainder + "," + divisor + "]"
    }
    case RunSat => AutomatonTask.keywords.sat
    case RunUnsat => AutomatonTask.keywords.unsat
    case RunEstablishment => AutomatonTask.keywords.est
    case RunNonEstablishment => AutomatonTask.keywords.nonest
    case RunGarbageFreedom => AutomatonTask.keywords.gf
    case RunWeakAcyclicity => AutomatonTask.keywords.acyc
    case RunMayHaveGarbage => AutomatonTask.keywords.garb
    case RunStrongCyclicity => AutomatonTask.keywords.cyc
    case RunReachability(from, to, negate) => negationPrefix(negate) + AutomatonTask.keywords.reach + "[" + from + "," + to + "]"
    case RunExactTracking(alloc, pure, negate) => negationPrefix(negate) + AutomatonTask.keywords.track + "[" + alloc.mkString(",") + (if (pure.nonEmpty) " : " + pure.mkString(",") else "") + "]"
    case RunRelaxedTracking(alloc, pure, negate) => negationPrefix(negate) + AutomatonTask.keywords.reltrack + "[" + alloc.mkString(",") + (if (pure.nonEmpty) " : " + pure.mkString(",") else "") + "]"
    case RunAllocationTracking(alloc, negate) => negationPrefix(negate) + AutomatonTask.keywords.alloc + "[" + alloc.mkString(",") + "]"
    case RunPureTracking(pure, negate) => negationPrefix(negate) + AutomatonTask.keywords.pure + "[" + pure.mkString(",") + "]"
  }

  def resultToString(isEmpty : Boolean) : String = this match {
    case RunHasPointer(negate : Boolean) => if (isEmpty != negate) "no alloc" else "alloc"
    case RunModulo(remainder : Int, divisor : Int, negate : Boolean) => (if (isEmpty) "all" else "ex.") + " #ptr " + (if (isEmpty != negate) "!= " else "== ") + remainder + "%" + divisor
    // TODO Other strings for negated automata?
    case RunExactTracking(alloc, pure, negate) => if (isEmpty) "no matching unf." else "ex. matching unf."
    case RunRelaxedTracking(alloc, pure, negate) => if (isEmpty) "no superset unf." else "ex. superset unf."
    case RunAllocationTracking(alloc, negate) => if (isEmpty) "no superset unf." else "ex. superset unf."
    case RunPureTracking(pure, negate) => if (isEmpty) "no superset unf." else "ex. superset unf."
    case RunSat => if (isEmpty) "all unsat" else "ex. sat"
    case RunUnsat => if (isEmpty) "all sat" else "ex. unsat"
    case RunEstablishment => if (isEmpty) "all non-est." else "ex. est."
    case RunNonEstablishment => if (isEmpty) "all est." else "ex. non-est"
    case RunReachability(from, to, negate) => if (isEmpty != negate) "all unreach" else "ex. reach"
    case RunGarbageFreedom => if (isEmpty) "all garbage" else "ex. garbage free"
    case RunWeakAcyclicity => if (isEmpty) "all cyclic" else "ex. weak. acyc."
    case RunMayHaveGarbage => if (isEmpty) "all garb. free" else "may ex. garb."
    case RunStrongCyclicity => if (isEmpty) "all weak. acyc" else "ex. strong. cyc."
  }

}

case class RunHasPointer(negate : Boolean = false) extends AutomatonTask

case class RunModulo(remainder : Int, divisor : Int, negate : Boolean = false) extends AutomatonTask {
  assert(remainder < divisor)
}

case class RunAllocationTracking(alloc : Set[Var], negate : Boolean = false) extends AutomatonTask

case class RunPureTracking(pure : Set[PureAtom], negate : Boolean = false) extends AutomatonTask

case class RunExactTracking(alloc : Set[Var], pure : Set[PureAtom], negate : Boolean = false) extends AutomatonTask

case class RunRelaxedTracking(alloc : Set[Var], pure : Set[PureAtom], negate : Boolean = false) extends AutomatonTask

case object RunSat extends AutomatonTask

case object RunUnsat extends AutomatonTask

case object RunEstablishment extends AutomatonTask

case object RunNonEstablishment extends AutomatonTask

case class RunReachability(from : Var, to : Var, negate : Boolean = false) extends AutomatonTask

case object RunGarbageFreedom extends AutomatonTask

case object RunWeakAcyclicity extends AutomatonTask

case object RunMayHaveGarbage extends AutomatonTask

case object RunStrongCyclicity extends AutomatonTask

object AutomatonTask {

  // TODO Clean this up a little bit. Is getting very long + somewhat repetitive
  def fromString(s : String) : Option[AutomatonTask] = s match {
    case "" => None
    case keywords.sat => Some(RunSat)
    case keywords.unsat => Some(RunUnsat)
    case keywords.hasptr => Some(RunHasPointer())
    case keywords.even => Some(RunModulo(0,2))
    case keywords.odd => Some(RunModulo(1,2))
    case keywords.est => Some(RunEstablishment)
    case keywords.nonest => Some(RunNonEstablishment)
    case keywords.acyc => Some(RunWeakAcyclicity)
    case keywords.cyc => Some(RunStrongCyclicity)
    case keywords.gf => Some(RunGarbageFreedom)
    case keywords.garb => Some(RunMayHaveGarbage)
    case other =>
      val res = Combinators.exceptionToNone("An exception occurred during parsing of " + other) {

        val modResult: Option[AutomatonTask] = for {
          input <- removeSurroundingKeyword(other, keywords.mod)
          params = input.split(",")
          if params.size == 2
          remainder = Integer.parseInt(params(0))
          divisor = Integer.parseInt(params(1))
        } yield RunModulo(remainder, divisor)

        val reachResult = for {
          input <- removeSurroundingKeyword(other, keywords.reach)
          params = input.split(",")
          if params.size == 2
        } yield RunReachability(mkVar(params(0)), mkVar(params(1)))

        val allocResult = for {
          input <- removeSurroundingKeyword(other, keywords.alloc)
          params = input.split(",")
          fvs = (params map mkVar).toSet[Var]
        } yield RunAllocationTracking(fvs)

        val pureResult = for {
          input <- removeSurroundingKeyword(other, keywords.pure)
          params = input.split(",")
          eqs = (params map parsePure).toSet
        } yield RunPureTracking(eqs)

        def trackParsing(constructor : (Set[Var], Set[PureAtom], Boolean) => AutomatonTask, kw : String)(input : String) : Option[AutomatonTask] =
          for {
            input <- removeSurroundingKeyword(other, kw)
            params : Array[String] = input.split(":")
            fvparams : Array[String] = params(0).trim.split(",")
            pureparams : Array[String] = if (params.size > 1) params(1).trim.split(",") else Array.empty
            fvs : Set[Var] = (fvparams map mkVar).toSet
            eqs = (pureparams map parsePure).toSet
          } yield constructor(fvs, eqs, false)

        val trackResult = trackParsing(RunExactTracking, keywords.track)(other)
        val relaxedTrackResult = trackParsing(RunRelaxedTracking, keywords.reltrack)(other)

        val successfulParses = Seq.empty ++ modResult ++ reachResult ++ allocResult ++ pureResult ++ trackResult ++ relaxedTrackResult
        successfulParses.headOption
      }

      if (res.isEmpty) println("Could not parse task " + other)

      res
  }

  private def parsePure(input : String) : PureAtom = {
    val (params, isEq) = if (input.contains("!=")) {
      (input.split("!="), false)
    } else if (input.contains("\u2249")) {
      (input.split("\u2249"), false)
    } else if (input.contains("\u2248")) {
      (input.split("\u2248"), true)
    } else (input.split("="), true)

    val (l,r)= (mkVar(params(0)), mkVar(params(1)))
    PureAtom(l,r,isEq)
  }

  private def mkVar(s: String) = {
    Var.stringTofreeOrNullVar(s.trim)
  }

  private def removeSurroundingKeyword(input : String, kw : String) : Option[String] = {
    if ((input.startsWith(kw + "(") && input.endsWith(")")) || (input.startsWith(kw + "[") && input.endsWith("]"))) {
      Some(input.drop(kw.length + 1).init)
    } else {
      None
    }
  }

  object keywords {
    val hasptr = "HASPTR"
    val mod = "MOD"
    val odd = "ODD"
    val even = "EVEN"
    val track = "TRACK"
    val reltrack = "REL-TR"
    val alloc = "ALLOC"
    val pure = "PURE"
    val sat = "SAT"
    val unsat = "UNSAT"
    val est = "EST"
    val nonest = "NON-EST"
    val gf = "GF"
    val garb = "GARB"
    val acyc = "ACYC"
    val cyc = "CYC"
    val reach = "REACH"
  }

}