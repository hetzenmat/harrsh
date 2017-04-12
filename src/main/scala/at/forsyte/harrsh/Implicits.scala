package at.forsyte.harrsh

import at.forsyte.harrsh.entailment.{GreedyUnfoldingModelChecker, Model}
import at.forsyte.harrsh.main.MainIO
import at.forsyte.harrsh.parsers.SIDParsers
import at.forsyte.harrsh.pure.EqualityBasedSimplifications
import at.forsyte.harrsh.refinement.DecisionProcedures.AnalysisResult
import at.forsyte.harrsh.refinement.{AutomatonTask, DecisionProcedures, RefinementAlgorithms}
import at.forsyte.harrsh.seplog.inductive.{Rule, SID, SIDUnfolding, SymbolicHeap}
import at.forsyte.harrsh.util.IOUtils

import scala.concurrent.duration
import scala.concurrent.duration.Duration
import scala.language.implicitConversions

/**
  * Created by jens on 4/7/17.
  */
object Implicits {

  private val InteractiveTimeout = Duration(30, duration.SECONDS)

  class ParsableString(val s : String) {

    def load() : SID = {
      IOUtils.findFileIn(s, Defaults.PathsToExamples) match {
        case Some(file) => MainIO.getSidFromFile(file)
        case None =>
          IOUtils.printWarningToConsole("Could not find file '" + s + "' in current path " + Defaults.PathsToExamples.mkString(":"))
          SID.empty("fail")
      }
    }

    def parseModel() : Model =  {
      IOUtils.findFileIn(s, Defaults.PathsToExamples) match {
        case Some(file) => MainIO.getModelFromFile(file)
        case None =>
          IOUtils.printWarningToConsole("Could not find file '" + s + "' in current path " + Defaults.PathsToExamples.mkString(":"))
          Model.empty
      }
    }

    def parse : SymbolicHeap = {
      SIDParsers.CombinedSIDParser.runOnSymbolicHeap(s) match {
        case Some(sh) => sh
        case None =>
          IOUtils.printWarningToConsole("Could not parse '" + s + "' as symbolic heap")
          SymbolicHeap.empty
      }
    }
  }

  class RichSID(val sid : SID) {

    def refineBy(task : AutomatonTask) : (SID,Boolean) = {
      RefinementAlgorithms.refineSID(sid, task.getAutomaton(sid.numFV), InteractiveTimeout, reportProgress = Defaults.reportProgress) match {
        case Some(refinedSID) =>
          refinedSID
        case None =>
          IOUtils.printWarningToConsole("Refinement failed")
          (SID.empty(sid.startPred),true)
      }
    }

    def decide(task : AutomatonTask) : Boolean = {
      val AnalysisResult(isEmpty, analysisTime, timedOut) = DecisionProcedures.decideInstance(sid, task.getAutomaton(sid.numFV), InteractiveTimeout, verbose = Defaults.reportProgress, reportProgress = Defaults.reportProgress)
      if (timedOut) {
        println("Reached timeout of " + InteractiveTimeout)
      } else {
        println("Finished analysis in " + analysisTime + "ms")
      }
      !isEmpty
    }

    def witness : SymbolicHeap = SIDUnfolding.firstReducedUnfolding(sid)

    def baseRule : Rule = {
      val base = sid.rules.filter(!_.body.hasPredCalls)
      if (base.size > 1) {
        IOUtils.printWarningToConsole("Warning: More than one base rule. Will pick arbitrary one")
      }
      base.head
    }

    def recursiveRule : Rule = {
      val rec = sid.rules.filter(_.body.hasPredCalls)
      if (rec.size > 1) {
        IOUtils.printWarningToConsole("Warning: More than one recursive rule. Will pick arbitrary one")
      }
      rec.head
    }
  }

  class RichSymbolicHeap(val sh : SymbolicHeap) {

    def unfoldFirstCall(by : SymbolicHeap) : SymbolicHeap = sh.replaceCall(sh.predCalls.head, by)
    def unfoldSecondCall(by : SymbolicHeap) : SymbolicHeap = sh.replaceCall(sh.predCalls(1), by)
    def unfoldIthCall(i : Int, by : SymbolicHeap) : SymbolicHeap = sh.replaceCall(sh.predCalls(i-1), by)
    def unfoldCalls(by : SymbolicHeap*) : SymbolicHeap = sh.replaceCalls(by)
    def unfoldAllCallsBy(by : SymbolicHeap) : SymbolicHeap = sh.replaceCalls(Seq.fill(sh.predCalls.size)(by))

    def unfoldOnce(sid : SID) : Iterable[SymbolicHeap] = SIDUnfolding.unfoldOnce(sid, Seq(sh))
    def unfoldings(sid : SID, depth : Int) : Iterable[SymbolicHeap] = SIDUnfolding.unfold(sid, depth)
    def reducedUnfoldings(sid : SID, depth : Int) : Iterable[SymbolicHeap] = SIDUnfolding.unfold(sid, depth, reducedOnly = true)

    def simplify : SymbolicHeap = EqualityBasedSimplifications.fullEqualitySimplification(sh)

    def isA(sid : SID) : Boolean = {
      println("Checking " + sh + " |= " + sid.callToStartPred)
      GreedyUnfoldingModelChecker.reducedEntailmentAsModelChecking(sh, sid.callToStartPred, sid, Defaults.reportProgress)
    }

    def refineBy(sid: SID, task : AutomatonTask) : (SID,Boolean) = {
      SID.fromTopLevelSH(sh, sid).refineBy(task)
    }

    def decide(sid: SID, task : AutomatonTask) : Boolean = {
      SID.fromTopLevelSH(sh, sid).decide(task)
    }
  }

  implicit def ruleToHeap(rule : Rule) : SymbolicHeap = rule.body

  implicit def sidToRichSID(sid : SID) : RichSID = new RichSID(sid)

  implicit def sidToRichSH(sh : SymbolicHeap) : RichSymbolicHeap = new RichSymbolicHeap(sh)

  implicit def stringToInteractiveString(s : String) : ParsableString = new ParsableString(s)

  implicit def stringToSH(s : String) : RichSymbolicHeap = s.parse

}