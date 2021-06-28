package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.Var

import scala.collection.mutable

/**
  * Like in a conversation with Jens: only compute types for the aliasing constraints whose domain equals to variables of the formula or predicate
  *
  * Representation of a type: Map from aliasing constraints to set of phi-types (unsat => set of types is empty)
  *
  * Fixed-point computation of predicates with worklist algorithm?
  */
class SmartTypeComputation {
//  val predicateTypes: mutable.Map[(String, AliasingConstraint[Var]), ]
}