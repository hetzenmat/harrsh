package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}
import com.typesafe.scalalogging.LazyLogging

import scala.annotation.tailrec
import scala.collection.mutable

// Test: remove x variables
class PredicateTypes(val sid: SID_btw, val x: Set[Var]) extends LazyLogging {
  //private val state: mutable.Map[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint), mutable.Set[PhiType]] = collection.mutable.Map.empty //.withDefaultValue(mutable.Set.empty)
  private var state: Map[String, Map[AliasingConstraint, Set[PhiType]]] = Map.empty
  private var finished: Set[AliasingConstraint] = Set.empty
  private var allFinished: Boolean = false

  def stateGet(s: String, ac: AliasingConstraint): Set[PhiType] = {
    state.getOrElse(s, Map.empty).getOrElse(ac, Set.empty)
  }

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

      val types = stateGet(pred.name, acExtendedRestricted)
      //val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(acPlaceholders, acExtended, types, sid)

      //println("Ext: " + typesExtended)
      val r = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, typesExtended, sid)

      r
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

//    if (!finished.contains(ac)) {
//      unfold(ac)
//    }

    if (!allFinished) unfold()


//    val allAcs = state.zipWithIndex.map(t => (t._1._1._2, t._2))
//    val keys = state.keySet
//    val allPreds = state.zipWithIndex.map(t => (t._1._1._1, t._2))

//    if (!state.contains((pred, ac))) {
//      println(state.toSeq.find(p => p._1 == (pred, ac)))
//      state.get((pred, ac))
//      println("sdf")
//    }

    if (!state(pred.name).contains(ac)) {
      println("sdf")
    }

    state(pred.name)(ac)

    // TODO Bug?
   // state.toSeq.find(p => p._1.equals((pred, ac))).get._2.toSet
  }

  private def unfold(/*ac: AliasingConstraint*/): Unit = {

    val xSubs = x.subsets(2) // .filter(_.nonEmpty).toSeq
    val allAcs = sid.predicates.values.flatMap(pred => xSubs.flatMap(xx => AliasingConstraint.allAliasingConstraints(pred.freeVars.union(xx)))).toSeq

    var changed = true
    var it = 0

    while (changed) {
      it += 1
      println("Unfold iteration " + it)

      changed = false

      var nac = 1
      for (ac <- allAcs) {
        println(nac + " / " + allAcs.size)
        nac += 1
        for (pred <- sid.predicates.values) {
          var newTypes = Set.empty[PhiType]

          for (rule <- pred.rules) {
            val discovered = ptypes(rule, ac)

            //println("discovered: " + discovered)
            newTypes = newTypes.union(Set.from(discovered))
            //newTypes.addAll(discovered)
          }

          if (!state.contains(pred.name)) state = state.updated(pred.name, Map.empty)

          if (state(pred.name).contains(ac)) {
            val prevSize = state(pred.name)(ac).size
            state = state.updated(pred.name, state(pred.name).updated(ac, state(pred.name)(ac).union(newTypes)))

            if (state(pred.name)(ac).size != prevSize) changed = true
          } else {
            state = state.updated(pred.name, state(pred.name).updated(ac, newTypes))
            changed = true
          }
        }
      }


      //finished = finished.incl(ac)
    }

    allFinished = true
  }


}
