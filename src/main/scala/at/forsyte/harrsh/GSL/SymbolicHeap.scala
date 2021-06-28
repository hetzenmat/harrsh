package at.forsyte.harrsh.GSL

import GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.SID.SID
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

sealed abstract class AbstractSymbolicHeap() {
  val atoms: Seq[Atom]

  final lazy val allVars: Set[Var] = atoms.flatMap(_.vars).toSet.excl(NullConst)
  final lazy val freeVars: Set[Var] = allVars.collect { case a: FreeVar => a }

  val isRecursive: Boolean
}

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

  override val atoms: Seq[Atom] = spatial ++ calls ++ equalities ++ disEqualities

  val lalloc: Set[Var] = spatial.map(_.from).toSet
  val lref: Set[Var] = spatial.flatMap(_.to).toSet

  def toBtw: SymbolicHeapBtw = SymbolicHeapBtw(quantifiedVars, spatial.head, calls, equalities, disEqualities)

  override val isRecursive: Boolean = calls.nonEmpty
}

sealed trait AbstractSymbolicHeapBtw extends AbstractSymbolicHeap

final case class SymbolicHeapBtw(quantifiedVars: Seq[String] = Seq(),
                                 pointsTo: PointsTo,
                                 calls: Seq[PredicateCall] = Seq(),
                                 equalities: Seq[Equality] = Seq(),
                                 disEqualities: Seq[DisEquality] = Seq()) extends AbstractSymbolicHeapBtw {
  override val atoms: Seq[Atom] = pointsTo +: (calls ++ equalities ++ disEqualities)

  override val isRecursive: Boolean = calls.nonEmpty

  def substitute(subst: Substitution[Var]): SymbolicHeapBtw = {
    SymbolicHeapBtw(quantifiedVars = quantifiedVars,
                    pointsTo = pointsTo.substitute(subst),
                    calls = calls.map(_.substitute(subst)),
                    equalities = equalities.map(_.substitute(subst)),
                    disEqualities = disEqualities.map(_.substitute(subst)))
  }

  def dropFirstQuantifiedVar(subst: Var): SymbolicHeapBtw = {
    require(!freeVars.contains(subst))
    require(quantifiedVars.nonEmpty)

    val ren: Substitution[Var] = Substitution.singleton((BoundVar(quantifiedVars.size), subst))

    SymbolicHeapBtw(quantifiedVars.dropRight(1),
                    pointsTo.substitute(ren),
                    calls.map(_.substitute(ren)),
                    equalities.map(_.substitute(ren)),
                    disEqualities.map(_.substitute(ren)))
  }

  def instantiate(pred: SID.Predicate[SymbolicHeapBtw], args: Seq[Int], substt: Map[Var, Int]): Option[RuleInstance] = {
    require(allVars.subsetOf(substt.keySet))

    val subst = substt.updated(NullConst, 0)

    if (equalities.exists({ case Equality(left, right) => subst(left) != subst(right) })) {
      return None
    }
    if (disEqualities.exists({ case DisEquality(left, right) => subst(left) == subst(right) })) {
      return None
    }

    val from = subst(pointsTo.from)
    val to = pointsTo.to.map(subst)
    val callsReplaced: Seq[(String, Seq[Int])] = calls.map(c => (c.pred, c.args.map(subst)))

    Some(RuleInstance(pred, args, from, to, callsReplaced))
  }

}

object SymbolicHeap {
  def buildSymbolicHeap(quantifiedVars: Seq[String], atoms: Seq[Atom]): SymbolicHeap = {

    val boundRenaming: Substitution[Var] = Substitution.from(quantifiedVars.zipWithIndex.map({ case (v, i) => (FreeVar(v), BoundVar(i + 1)) }))
    val renamedAtoms: Seq[Atom#T] = atoms.map(_.substitute(boundRenaming))

    SymbolicHeap(quantifiedVars,
                 spatial = renamedAtoms.collect { case a: PointsTo => a },
                 calls = renamedAtoms.collect { case a: PredicateCall => a },
                 equalities = renamedAtoms.collect { case a: Equality => a },
                 disEqualities = renamedAtoms.collect { case a: DisEquality => a })
  }
}