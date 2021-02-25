package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}
import com.typesafe.scalalogging.LazyLogging

import scala.annotation.tailrec
import scala.collection.mutable

class PredicateTypes(val sid: SID_btw) extends LazyLogging {
  private val state: mutable.Map[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint), mutable.Set[PhiType]] = collection.mutable.Map.empty.withDefaultValue(mutable.Set.empty)
  private val finished: mutable.Set[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint)] = mutable.Set.empty

  private val TC = new TypeComputation(sid, Set.empty)

  def ptypes(atom: Atom, ac: AliasingConstraint): Iterable[PhiType] = atom match {
    case e: Equality => TC.types(e, ac)
    case d: DisEquality => TC.types(d, ac)
    case p: PointsTo => TC.types(p, ac)
    case PredicateCall(predName, args) =>
      val pred = sid.predicates(predName)

      val parameters = pred.args.map(FreeVar)

      val acExtended = ac.reverseRenaming(parameters, args)
      val acExtendedRestricted = acExtended.restricted(ac.domain.union(parameters.toSet))

      val types = state((pred, acExtendedRestricted))
      val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(ac, acExtended, typesRenamed)

      typesExtended
  }

  def ptypes(atoms: Seq[Atom], ac: AliasingConstraint): Iterable[PhiType] = atoms match {
    case atom +: Seq() => ptypes(atom, ac)
    case head +: rest => PhiType.composition(sid, ptypes(head, ac), ptypes(rest, ac))
  }

  def ptypes(sh: SymbolicHeapBtw, ac: AliasingConstraint): Iterable[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(ac.domain.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sh.dropFirstQuantifiedVar(fresh), ac_)
        PhiType.forget(sid, ac_, fresh, types)
      })
    } else ptypes(sh.atoms, ac)

  /**
    * @param predicateCall The predicate call whose type shall be computed
    * @param ac            The aliasing constraint of the actual arguments
    */
  def computeTypes(predicateCall: PredicateCall, ac: AliasingConstraint): Iterable[PhiType] = {
    val pred = sid.predicates(predicateCall.pred)
    require(pred.args.length == predicateCall.args.length)
    require((pred.args.map(FreeVar).toSet[Var] intersect predicateCall.args.toSet).isEmpty)

    unfold(pred, predicateCall.args, ac)
  }

  @tailrec
  private def unfold(pred: SID.Predicate[SymbolicHeapBtw], args: Seq[Var], ac: AliasingConstraint): mutable.Set[PhiType] = {
    val subst: Map[Var, Var] = pred.args.map(FreeVar).zip(args).toMap
    val tuple = (pred, ac)
    if (finished contains tuple) {
      state(tuple)
    } else {
      val newTypes = mutable.Set.empty[PhiType]
      for (rule <- pred.rules) {
        val renamed = rule.substitute(subst)
        val discovered = ptypes(renamed, ac)
        newTypes.addAll(discovered)
      }

      if (state(tuple) == newTypes) {
        finished.add(tuple)
        state(tuple)
      } else {
        state(tuple).addAll(newTypes)
        unfold(pred, args, ac)
      }
    }
  }
}
