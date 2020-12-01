package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.seplog.{FreeVar, Renaming, Var}
import PlaceholderVar._
import at.forsyte.harrsh.seplog.inductive.SymbolicHeap

import scala.util.Try

case class PlaceholderVar(index: Int) {

  def toFreeVar : FreeVar = FreeVar(placeholderPrefix + index)

}

object PlaceholderVar {

  val placeholderPrefix = "?"

  def fromVar(v: Var) : Option[PlaceholderVar] = v match {
    case FreeVar(name) =>
      if (name startsWith placeholderPrefix) {
        Try { Integer.parseInt(name.drop(placeholderPrefix.length)) }.toOption.map(PlaceholderVar(_))
      } else {
        None
      }
    case _ => None
  }

  def getIndex(v: Var) : Int = fromVar(v) match {
    case Some(PlaceholderVar(index)) => index
    case None => throw new IllegalArgumentException("Trying to get placeholder index of non-placeholder var " + v)
  }

  def replaceVarsWithPlaceholders(sh: SymbolicHeap, vars: Seq[Var]): SymbolicHeap = {
    val allUnusedPlaceholders: Seq[Var] = PlaceholderVar.allUnusedPlaceholders(used = Set.empty)
    val boundVarsToPlaceholders = vars.zip(allUnusedPlaceholders).toMap
    val renaming = Renaming.fromMap(boundVarsToPlaceholders)
    // We keep the order of the original FVs unchanged and append any additional free vars introduced (by replacing bound vars by free vars)
    val renamedFvs = sh.freeVars map (renaming(_))
    val additionalFvs = boundVarsToPlaceholders.filterNot(_._1.isFree).values
    val newFvs = renamedFvs ++ additionalFvs
    sh.rename(renaming, Some(newFvs.map(_.asInstanceOf[FreeVar])))
  }

  def isPlaceholder(v : Var): Boolean = fromVar(v).nonEmpty

  def isNonPlaceholderNonNullFreeVar(v: Var): Boolean = v.isFreeNonNull && !isPlaceholder(v)

  def isNonPlaceholderFreeVar(v: Var): Boolean = v.isFree && !isPlaceholder(v)

  def max(pvs: Iterable[PlaceholderVar]): PlaceholderVar = try {
    pvs.maxBy(_.index)
  } catch {
    case e: UnsupportedOperationException => PlaceholderVar(0)
  }

  def maxIndex(pvs: Set[PlaceholderVar]): Int = max(pvs).index

  def min(pvs: Iterable[PlaceholderVar]): PlaceholderVar = try {
    pvs.minBy(_.index)
  } catch {
    case e: UnsupportedOperationException => PlaceholderVar(0)
  }

  def allUnusedPlaceholders(used: Set[PlaceholderVar]): LazyList[FreeVar] = {
    for {
      i <- LazyList.from(0)
      pv = PlaceholderVar(i)
      if !used.contains(pv)
    } yield pv.toFreeVar
  }

  def containsNoRedundantPlaceholder(vs: Set[Var]): Boolean = {
    // There's at most one placeholder in the set and if there's one in the set it's the only element
    val numPhs = vs.count(PlaceholderVar.isPlaceholder)
    numPhs <= 1 && (numPhs == 0 || vs.size == 1)
  }

  def noGapsInPlaceholders(phs: Iterable[PlaceholderVar]): Boolean = {
    phs.isEmpty || phs.map(_.index).max == phs.size
  }

  def placeholderClashAvoidanceUpdate(phs: Set[PlaceholderVar]) : ConstraintUpdater = {
    val maxPv = max(phs)
    val shiftBy = maxPv.index
    BijectiveRenamingUpdate(s"Placeholder clash avoidance update with shift $shiftBy",
      fv => fromVar(fv) match {
        case Some(PlaceholderVar(value)) => PlaceholderVar(value + shiftBy).toFreeVar
        case None => fv
      })
  }

}
