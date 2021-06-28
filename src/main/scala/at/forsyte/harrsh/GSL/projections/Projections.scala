package at.forsyte.harrsh.GSL.projections

import at.forsyte.harrsh.GSL.{AliasingConstraint, Env, GslFormula}
import at.forsyte.harrsh.GSL.GslFormula.Atom.PointsTo
import at.forsyte.harrsh.seplog
import at.forsyte.harrsh.seplog.NullConst

object Projections {
  val StackForestProjection = optimized.StackForestProjection
  type StackForestProjection = optimized.StackForestProjection

  val TreeProjection = optimized.TreeProjection
  type TreeProjection = optimized.TreeProjection.TreeProjection

  type Var = optimized.TreeProjection.Var
  val NULL: Var = 0


  @inline def toUniversal(i: Int): Var = i

  def isFree(v: Var): Boolean = v > 0

  def isBound(v: Var): Boolean = v < 0

  def stringToFreeVar(s : String): Var = Env.varForward(s)

//  type StackForestProjection = prototype.StackForestProjection
//  val StackForestProjection = prototype.StackForestProjection
//
//  type TreeProjection = prototype.TreeProjection
//  val TreeProjection = prototype.TreeProjection
//
//  type Var = seplog.Var
//  val NULL: Var = seplog.NullConst
//
//  @inline def getVars(f : GslFormula): Set[Var] = f.vars
}
