package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}

object TypeComputation {

  type PredTypes = (SID.Predicate[SymbolicHeap], AliasingConstraint) => Set[PhiType]

  def ptypes(sid: SID, x: Set[Var], p: PredTypes, atom: Atom, ac: AliasingConstraint): Set[PhiType] = atom match {
    case Equality(left, right) => if (ac =:= (left, right)) Set(PhiType(Set())) else Set()
    case DisEquality(left, right) => if (ac =:= (left, right)) Set() else Set(PhiType(Set()))
    case pointsTo: PointsTo => Set(PhiType.ptrmodel(ac, pointsTo))
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

  def ptypes(sid: SID, x: Set[Var], p: PredTypes, atoms: Seq[Atom], ac: AliasingConstraint): Set[PhiType] = atoms match {
    case atom +: Seq() => ptypes(sid, x, p, atom, ac)
    case head +: rest => PhiType.composition(sid, ptypes(sid, x, p, head, ac), ptypes(sid, x, p, rest, ac))
  }

  def ptypes(sid: SID, x: Set[Var], p: PredTypes, sh: SymbolicHeap, ac: AliasingConstraint): Set[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(x.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sid, x, p, sh.dropFirstQuantifiedVar(fresh), ac_)
        PhiType.forget(sid, ac_, fresh, types)
      })
    } else ptypes(sid, x, p, sh.atoms, ac)

}
