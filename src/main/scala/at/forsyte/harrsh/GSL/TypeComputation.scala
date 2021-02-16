package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}

object TypeComputation {

  type PredTypes = (SID.Predicate[SymbolicHeap], AliasingConstraint) => Set[PhiType]
  type PredTypesMap = Map[(SID.Predicate[SymbolicHeap], AliasingConstraint), Set[PhiType]]

  def ptypes(sid: SID, x: Set[Var], p: PredTypesMap, atom: Atom, ac: AliasingConstraint): Set[PhiType] = atom match {
    case Equality(left, right) => if (ac =:= (left, right)) Set(PhiType(LazyList.empty)) else Set()
    case DisEquality(left, right) => if (ac =:= (left, right)) Set() else Set(PhiType(LazyList.empty))
    case pointsTo: PointsTo => Set(PhiType.ptrmodel(sid, ac, pointsTo))
    case PredicateCall(predName, args) =>
      val pred = sid.predicates(predName)

      val parameters = pred.args.map(FreeVar)

      val acExtended = ac.reverseRenaming(parameters, args)
      val acExtendedRestricted = acExtended.restricted(x.union(parameters.toSet))

      val types = p(pred, acExtendedRestricted)
      val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(ac, acExtended, typesRenamed)

      typesExtended
  }

  def ptypes(sid: SID, x: Set[Var], p: PredTypesMap, atoms: Seq[Atom], ac: AliasingConstraint): Set[PhiType] = atoms match {
    case atom +: Seq() => ptypes(sid, x, p, atom, ac)
    case head +: rest => PhiType.composition(sid, ptypes(sid, x, p, head, ac), ptypes(sid, x, p, rest, ac))
  }

  def ptypes(sid: SID, x: Set[Var], p: PredTypesMap, sh: SymbolicHeap, ac: AliasingConstraint): Set[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(x.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sid, x, p, sh.dropFirstQuantifiedVar(fresh), ac_)
        PhiType.forget(sid, ac_, fresh, types)
      })
    } else ptypes(sid, x, p, sh.atoms, ac)

  def unfold(sid: SID, x: Set[Var], p: PredTypesMap): PredTypesMap = {



    Map.empty
  }

  def lfpUnfold(sid: SID, x: Set[Var]): PredTypesMap = {
    Map.empty
  }
}
