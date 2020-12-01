package at.forsyte.harrsh.seplog.inductive

import at.forsyte.harrsh.main.HarrshLogging
import at.forsyte.harrsh.seplog.Var.Naming
import at.forsyte.harrsh.seplog.{Renaming, Var}
import at.forsyte.harrsh.util.ToLatex
import at.forsyte.harrsh.util.ToLatex._

import scala.collection.immutable.SortedSet

/**
  * Created by jkatelaa on 10/3/16.
  */
case class PureAtom(l: Var, r: Var, isEquality: Boolean) extends SepLogAtom with HarrshLogging {

  override def isSpatial = false

  override def isPure = true

  override def toSymbolicHeap = SymbolicHeap(Seq(this), Seq.empty, Seq.empty, Var.freeNonNullVars(Seq(l,r)))

  override def renameVars(f: Renaming): PureAtom = PureAtom(l.rename(f), r.rename(f), isEquality)

  override def getVars : SortedSet[Var] = SortedSet.empty[Var].incl(l).incl(r)

  def comparesFree: Boolean = getNonNullVars.forall(_.isFree)

  def isPointerComparison = true

  def isOrdered: Boolean = l <= r

  def ordered: PureAtom = if (isOrdered) this else PureAtom(r, l, isEquality)

  def isTautology: Boolean = isEquality && l == r

  def isConsistent: Boolean = isEquality || l != r

  override def toStringWithVarNames(names: Naming): String = {
    val op = if (isEquality) " \u2248 " else " \u2249 "
    names(l) + op + names(r)
  }

}

object PureAtom {

  implicit val pureAtomToLatex: ToLatex[PureAtom] = (atom: PureAtom, naming: Naming) => {
    atom.l.toLatex(naming) + (if (atom.isEquality) " = " else " \\neq ") + atom.r.toLatex(naming)
  }

}