package at.forsyte.harrsh.seplog.inductive

import at.forsyte.harrsh.seplog.Var.Naming
import at.forsyte.harrsh.seplog.{NullConst, Renaming, Var}
import at.forsyte.harrsh.util.ToLatex
import at.forsyte.harrsh.util.ToLatex._

import scala.collection.immutable.SortedSet

/**
  * Created by jens on 2/28/17.
  */

/**
  * Inductive spatial predicate, whose semantics is given by a SID
  * @param name Name of the predicate
  * @param args Nonempty sequence of arguments
  */
case class PredCall(name : String, args : Seq[Var]) extends SepLogAtom {
  override def toStringWithVarNames(names: Naming): String = name + "(" + args.map(names).mkString(",") + ")"

  override def isSpatial: Boolean = true

  override def isPure: Boolean = false

  override def toSymbolicHeap: SymbolicHeap = SymbolicHeap(Seq.empty, Seq.empty, Seq(this), Var.freeNonNullVars(args))

  override def renameVars(f: Renaming): PredCall = copy(args = args map (_.rename(f)))

  override def getVars : SortedSet[Var] = SortedSet.empty[Var] ++ args
}

object PredCall {
  implicit val predCallToLatex: ToLatex[PredCall] = (predCall: PredCall, naming: Naming) => {
    val argString = predCall.args.map(_.toLatex(naming)).mkString(",")
    s"\\RuleName{${Predicate.predicateHeadToLatex(predCall.name)}}($argString)"
  }
}