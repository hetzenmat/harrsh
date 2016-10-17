package slex.seplog

import slex.Combinators

/**
  * Created by jkatelaa on 9/30/16.
  */
trait SepLogFormula {

  def isSpatial : Boolean

  def isPure : Boolean

  def isSymbolicHeap : Boolean

  def toSymbolicHeap : Option[SymbolicHeap]

  // TODO: This renames both free and bound variables. Might need something more sophisticated like proper alpha conversion in the future. (See Exists)
  def renameVars(f : String => String) : SepLogFormula
}

case class Neg(phi : SepLogFormula) extends SepLogFormula {
  override def toString = "(\u00ac " + phi + ")"

  override def isSpatial: Boolean = phi.isSpatial

  override def isPure: Boolean = phi.isPure

  // Symbolic heaps are not closed under negation
  override def isSymbolicHeap: Boolean = false

  override def toSymbolicHeap: Option[SymbolicHeap] = None

  override def renameVars(f : String => String) = Neg(phi.renameVars(f))
}

case class And(phi : SepLogFormula, psi : SepLogFormula) extends SepLogFormula {
  override def toString = "(" + phi + " \u2227 " + psi + ")"

  override def isSpatial: Boolean = phi.isSpatial || psi.isSpatial

  override def isPure: Boolean = phi.isPure && psi.isPure

  // The conjunction of two pure formulas is a symbolic heap
  override def isSymbolicHeap: Boolean = isPure && phi.isSymbolicHeap && psi.isSymbolicHeap

  override def toSymbolicHeap: Option[SymbolicHeap] = SymbolicHeap.combineHeaps(phi.toSymbolicHeap, psi.toSymbolicHeap)

  override def renameVars(f : String => String) = And(phi.renameVars(f), psi.renameVars(f))
}

case class Or(phi : SepLogFormula, psi : SepLogFormula) extends SepLogFormula {
  override def toString = "(" + phi + " \u2228 " + psi + ")"

  override def isSpatial: Boolean = phi.isSpatial || psi.isSpatial

  override def isPure: Boolean = phi.isPure && psi.isPure

  // Symbolic heaps are not closed under disjunction
  override def isSymbolicHeap: Boolean = false

  override def toSymbolicHeap: Option[SymbolicHeap] = None

  override def renameVars(f : String => String) = Or(phi.renameVars(f), psi.renameVars(f))
}

case class Exists(varid : String, phi : SepLogFormula) extends SepLogFormula {
  override def toString = "(\u2203 "  + varid + " . " + phi + ")"

  override def isSpatial: Boolean = phi.isSpatial

  override def isPure: Boolean = phi.isPure

  override def isSymbolicHeap: Boolean = phi.isSymbolicHeap

  override def toSymbolicHeap: Option[SymbolicHeap] = phi.toSymbolicHeap map {
    case SymbolicHeap(pure, spatial, qvars) => SymbolicHeap(pure, spatial, varid :: qvars.toList)
  }

  // TODO Note that we transform bound variables as well. Might have to change that in the future
  override def renameVars(f : String => String) = Exists(f(varid), phi.renameVars(f))
}

case class SepCon(phi : SepLogFormula, psi : SepLogFormula) extends SepLogFormula {
  override def toString = "(" + phi + " * " + psi + ")"

  override def isSpatial: Boolean = phi.isSpatial || psi.isSpatial

  // * of two pure formulas is equivalent to their conjunction
  override def isPure: Boolean = phi.isPure && psi.isPure

  // The separating conjunction of two symbolic heaps is a symbolic heap
  override def isSymbolicHeap: Boolean = phi.isSymbolicHeap && psi.isSymbolicHeap

  override def toSymbolicHeap: Option[SymbolicHeap] = SymbolicHeap.combineHeaps(phi.toSymbolicHeap, psi.toSymbolicHeap)

  override def renameVars(f : String => String) = SepCon(phi.renameVars(f), psi.renameVars(f))
}

object SepLogFormula {

  def fromPureAtoms(atoms : Seq[PureAtom]) : PureFormula = Combinators.iteratedBinOp[PureFormula](PureAnd, True())(atoms)

  def fromSpatialAtoms(atoms : Seq[SpatialAtom]) : SepLogFormula = Combinators.iteratedBinOp[SepLogFormula](SepCon, Emp())(atoms)

}