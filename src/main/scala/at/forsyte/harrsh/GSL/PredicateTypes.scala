package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}
import com.typesafe.scalalogging.LazyLogging

import scala.annotation.tailrec
import scala.collection.mutable

// Test: remove x variables
class PredicateTypes(val sid: SID_btw, val x: Set[Var]) extends LazyLogging {
  private val state: mutable.Map[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint), mutable.Set[PhiType]] = collection.mutable.Map.empty.withDefaultValue(mutable.Set.empty)
  private val finished: mutable.Set[AliasingConstraint] = mutable.Set.empty


  def ptypes(atom: Atom, ac: AliasingConstraint): Iterable[PhiType] = atom match {
    case e: Equality => TypeComputation.equality(e, ac)
    case d: DisEquality => TypeComputation.disEquality(d, ac)
    case p: PointsTo =>
      val r = Set(PhiType.ptrmodel(sid, ac, p))
      r
    case PredicateCall(predName, args) =>
      val pred = sid.predicates(predName)

      val parameters = pred.args.map(FreeVar)

      // Replace variables in current ac that are also parameters by placeholders

      val parametersPlaceholders = parameters.zipWithIndex.map(t => (t._1, FreeVar("?" + (t._2 + 1))))

      val subst: Map[Var, Var] = parametersPlaceholders.toMap
      val acPlaceholders = ac.rename(subst)
      val argsPlaceholders = args.map(v => subst.getOrElse(v, v))

      require((parameters intersect argsPlaceholders).isEmpty)
      val acExtended = acPlaceholders.reverseRenaming(parameters, argsPlaceholders)

      val acExtendedRestricted = acExtended.restricted(x union parameters.toSet)

      val types = state((pred, acExtendedRestricted))
      //val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(acPlaceholders, acExtended, types)

      //println("Ext: " + typesExtended)
      PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, typesExtended)
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

  def getType(pred: SID.Predicate[SymbolicHeapBtw], ac: AliasingConstraint): Set[PhiType] = {
    if (!finished.contains(ac)) {
      unfold(ac)
    }

    state((pred, ac)).toSet
  }

  private def unfold(ac: AliasingConstraint): Unit = {

    var changed = true
    var it = 0

    while (changed) {
      it += 1
      println("Unfold iteration " + it)

      changed = false
      for (pred <- sid.predicates.values) {
        val newTypes = mutable.Set.empty[PhiType]

        for (rule <- pred.rules) {

          val discovered = ptypes(rule, ac)
          //println("discovered: " + discovered)
          newTypes.addAll(discovered)
        }

        val prevSize = state((pred, ac)).size
        state((pred, ac)).addAll(newTypes)

        if (state((pred, ac)).size != prevSize) changed = true
      }
    }

    finished.add(ac)
  }


}
