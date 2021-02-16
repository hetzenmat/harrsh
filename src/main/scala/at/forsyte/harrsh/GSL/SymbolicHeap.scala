package at.forsyte.harrsh.GSL

import GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}

sealed abstract class AbstractSymbolicHeap()

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent a symbolic heap.
  * Quantified variables are represented by bound variables starting with index 1.
  */
final case class SymbolicHeap(quantifiedVars: Seq[String],
                              spatial: Seq[PointsTo],
                              calls: Seq[PredicateCall],
                              equalities: Seq[Equality],
                              disEqualities: Seq[DisEquality]) extends AbstractSymbolicHeap {
  val allVars: Set[Var] = (spatial ++ calls ++ equalities ++ disEqualities).flatMap(_.vars).toSet

  val freeVars: Set[Var] = allVars.collect { case a: FreeVar => a }

  val lalloc: Set[Var] = spatial.map(_.from).toSet
  val lref: Set[Var] = spatial.flatMap(_.to).toSet

  val atoms: Seq[Atom] = spatial ++ calls ++ equalities ++ disEqualities

  def toPointerClosedSymbolicHeap: PointerClosedSymbolicHeap =
    PointerClosedSymbolicHeap(quantifiedVars,
                              calls ++ spatial.map({ case PointsTo(from, to) => PredicateCall("ptr" + to.size, Seq(from) ++ to) }),
                              equalities,
                              disEqualities)

  def instantiate(predName: String, args: Seq[Int], subst: Map[Var, Int]): Option[RuleInstance] = {
    require(allVars.subsetOf(subst.keySet))

    if (equalities.exists({ case Equality(left, right) => subst(left) != subst(right) })) {
      return None
    }
    if (disEqualities.exists({ case DisEquality(left, right) => subst(left) == subst(right) })) {
      return None
    }
    if (spatial.size != 1) {
      return None
    }

    val from = subst(spatial.head.from)
    val to = spatial.head.to.map(subst)
    val callsReplaced: Seq[(String, Seq[Int])] = calls.map(c => (c.pred, c.args.map(subst)))

    Some(RuleInstance(predName, args, from, to, callsReplaced))
  }

  def dropFirstQuantifiedVar(subst: Var): SymbolicHeap = {
    require(!freeVars.contains(subst))
    require(quantifiedVars.nonEmpty)

    val ren: Map[Var, Var] = Map((BoundVar(quantifiedVars.size), subst))

    SymbolicHeap(quantifiedVars.dropRight(1),
                 spatial.map(_.substitute(ren)),
                 calls.map(_.substitute(ren)),
                 equalities.map(_.substitute(ren)),
                 disEqualities.map(_.substitute(ren)))
  }
}

final case class PointerClosedSymbolicHeap(quantifiedVars: Seq[String],
                                           calls: Seq[PredicateCall],
                                           equalities: Seq[Equality],
                                           disEqualities: Seq[DisEquality]) extends AbstractSymbolicHeap {
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