package at.forsyte.harrsh.GSL

import GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a symbolic heap
  */
case class SymbolicHeap(quantifiedVars: Seq[String],
                        spatial: Seq[PointsTo],
                        calls: Seq[PredicateCall],
                        equalities: Seq[Equality],
                        disEqualities: Seq[DisEquality]) {
  val allVars: Set[Var] = (spatial ++ calls ++ equalities ++ disEqualities).foldLeft(Set.empty[Var]) { (set, atom) =>
    set.union(atom.vars)
  }

  val freeVars: Set[Var] = allVars.collect { case a: FreeVar => a }

  val lalloc: Set[Var] = spatial.map(_.from).toSet
  val lref: Set[Var] = spatial.flatMap(_.to).toSet
}

object SymbolicHeap {
  def buildSymbolicHeap(quantifiedVars: Seq[String], atoms: Seq[Atom]): SymbolicHeap = {

    val boundRenaming: Map[Var, Var] = quantifiedVars.zipWithIndex.map({ case (v, i) => (FreeVar(v), BoundVar(i + 1)) }).toMap
    val renamedAtoms: Seq[Atom] = atoms.map(_.substitute(boundRenaming))

    SymbolicHeap(quantifiedVars,
      spatial = renamedAtoms.collect { case a: PointsTo => a },
      calls = renamedAtoms.collect { case a: PredicateCall => a },
      equalities = renamedAtoms.collect { case a: Equality => a },
      disEqualities = renamedAtoms.collect { case a: DisEquality => a })
  }
}