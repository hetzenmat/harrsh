package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.GSL.SID.Predicate
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.{immutable, mutable}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}

class PredicateTypes(val sid: SID_btw, val x: Set[Var]) extends LazyLogging {

  private type LookupFunction = (Predicate[SymbolicHeapBtw], AliasingConstraint) => Iterable[PhiType]

  private val state: mutable.Map[String, mutable.Map[AliasingConstraint, mutable.Set[PhiType]]] = mutable.Map.empty
  private val table: mutable.Map[Int, mutable.Map[(String, AliasingConstraint), Set[PhiType]]] = mutable.Map.empty
  private val nonRecursiveTypes: mutable.Map[(SymbolicHeapBtw, AliasingConstraint), Set[PhiType]] = mutable.Map.empty
  private val finished: mutable.Set[(String, AliasingConstraint)] = mutable.Set.empty
  private var allFinished: Boolean = false
  val queue: mutable.Queue[(AliasingConstraint, SID.Predicate[SymbolicHeapBtw])] = mutable.Queue.empty
  val iterations: mutable.Map[(String, AliasingConstraint), Int] = mutable.Map.empty
  var changed: Boolean = false
  //val predProgress: mutable.Map[(String, AliasingConstraint), Int] = mutable.Map.empty

  private def stateGet(s: String, ac: AliasingConstraint): mutable.Set[PhiType] = {
    state.getOrElse(s, mutable.Map.empty).getOrElse(ac, mutable.Set.empty)
  }

  def ptypes(atom: Atom, ac: AliasingConstraint, lookup: LookupFunction): Iterable[PhiType] = atom match {
    case e: Equality => TypeComputation.equality(e, ac)
    case d: DisEquality => TypeComputation.disEquality(d, ac)
    case p: PointsTo => TypeComputation.pointsTo(p, ac, sid)
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

      val acExtendedRestricted = acExtended.restricted((x union parameters.toSet).incl(NullConst))

      //      val types = stateGet(pred.name, acExtendedRestricted)
      //      val types = unfoldLazy(it, pred, acExtendedRestricted)
      val substMax = acExtended.domain.map(v => (v, acExtended.largestAlias(v))).toMap

      val types = lookup(pred, acExtendedRestricted) //.map(_.substitute(substMax))

      //val typesExtended = PhiType.extend(acPlaceholders, acExtended, types, sid) TODO RECHEK
      val typesExtended = PhiType.extend(acExtendedRestricted, acExtended, types, sid)

      val substMax2 = ac.domain.map(v => (v, ac.largestAlias(v))).toMap
      val r = PhiType.rename(parameters ++ parametersPlaceholders.map(_._2), args.asInstanceOf[Seq[FreeVar]] ++ parametersPlaceholders.map(_._1), ac, typesExtended, sid).map(_.substitute(substMax2))

      //r.map(_.substitute(substMax))
      if (Utils.nonCanonical(r, ac)) {
        println("sdf")
      }
      r
  }

  def ptypes(atoms: Seq[Atom], ac: AliasingConstraint, lookup: LookupFunction): Iterable[PhiType] = atoms match {
    case atom +: Seq() => ptypes(atom, ac, lookup)
    case head +: rest => PhiType.composition(sid, ptypes(head, ac, lookup), ptypes(rest, ac, lookup), ac)
  }

  def ptypes(sh: SymbolicHeapBtw, ac: AliasingConstraint, lookup: LookupFunction): Iterable[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(ac.domain.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sh.dropFirstQuantifiedVar(fresh), ac_, lookup)

        val r = PhiType.forget(sid, ac_, fresh, types)
        r
      })
    } else ptypes(sh.atoms, ac, lookup)


  def unfoldLazy(it: Integer, pred: SID.Predicate[SymbolicHeapBtw], ac: AliasingConstraint): Set[PhiType] = {


    if (it == 0) {

      //      sid.predicates.values.filter(_.rules.exists(!_.isRecursive)).foreach { nonRecursive =>
      //        val types = ptypesIterationParallel(ac, nonRecursive, (_, _) => Set.empty)
      //        table(0).put((pred.name, ac), types)
      //      }
      //
      //      sid.predicates.values.filter(_.rules.forall(!_.isRecursive)).foreach { recursive =>
      //        val types = ptypesIterationParallel(ac, recursive, (p, a) => unfoldLazy(0, p, a))
      //        table(0).put((pred.name, ac), types)
      //      }
      //
      //      return table(0)((pred.name, ac))

      return Set.empty
    }

    require(it > 0)

    if (!table.contains(it))
      table.put(it, mutable.Map.empty)

    println(it + " " + pred.name + " " + ac)

    if (table(it).contains((pred.name, ac))) {
      val ret = table(it)((pred.name, ac))

      //      println(ret)

      if (Utils.nonCanonical(ret, ac) || ret.exists(_.projections.exists(!_.isDelimited(sid)))) {
        ???
      }

      ret
    } else {

      val newTypes = mutable.Set.empty[PhiType]
      for (rule <- pred.rules) {
        if (rule.isRecursive) {
          val discovered = ptypes(rule, ac, (p, a) => unfoldLazy(it - 1, p, a))
          /*val discovered = ptypes(rule, ac, (p, a) => {
            val i = predProgress.getOrElse((p.name, a), 0)
            unfoldLazy(Math.max(i, it - 1), p, a)
          })*/
          newTypes.addAll(discovered)
        } else {
          if (!nonRecursiveTypes.contains((rule, ac))) {
            nonRecursiveTypes.put((rule, ac), Set.from(ptypes(rule, ac, (_, _) => ???)))
          }

          newTypes.addAll(nonRecursiveTypes((rule, ac)))
        }
      }

      table(it).put((pred.name, ac), Set.from(newTypes))
      //predProgress.updateWith((pred.name, ac))(Function.const(Some(it)))

      val ret = table(it)((pred.name, ac))

      //      println(ret)

      if (Utils.nonCanonical(ret, ac) || ret.exists(_.projections.exists(!_.isDelimited(sid)))) {
        ???
      }

      if (ret.size > unfoldLazy(it - 1, pred, ac).size)
        changed = true

      ret
    }
  }

  def getTypeLazy(pred: SID.Predicate[SymbolicHeapBtw], ac: AliasingConstraint): Set[PhiType] = {

    var current = 1
    while (table.contains(current) && table(current).contains((pred.name, ac))) {
      current += 1
    }

    changed = true
    var result: Set[PhiType] = Set.empty
    var streak = 0
    while (streak < 2) {

      streak += 1
      changed = false
      result = unfoldLazy(current, pred, ac)
      current += 1

      if (changed)
        streak = 0
    }


//    result = table(current - 1)((pred.name, ac))

//    if (result != unfoldLazy(current, pred, ac)) {
//      print("")
//    }
//    require(result == unfoldLazy(current, pred, ac))

    val r = result.flatMap(t => PhiType.from(t.projections.filter(_._isDelimited(sid)), sid, ac))

    r
  }

  def getType(pred: SID.Predicate[SymbolicHeapBtw], ac: AliasingConstraint): Set[PhiType] = {
    if (!allFinished) unfold()

    state(pred.name)(ac).toSet
  }

  private def ptypesIterationSequential(ac: AliasingConstraint, pred: Predicate[SymbolicHeapBtw]): Set[PhiType] = {
    val newTypes = mutable.Set.empty[PhiType]
    for (rule <- pred.rules) {
      val discovered = ptypes(rule, ac, (p, a) => stateGet(p.name, a))

      newTypes.addAll(discovered)
    }

    newTypes.toSet
  }

  private def ptypesIterationParallel(ac: AliasingConstraint,
                                      pred: Predicate[SymbolicHeapBtw],
                                      lookup: LookupFunction,
                                      ruleFilter: SymbolicHeapBtw => Boolean = Function.const(true)): Set[PhiType] = {
    val futures: Seq[Future[Set[PhiType]]] = pred.rules.filter(ruleFilter).map(rule => Future {
      immutable.Set.from(ptypes(rule, ac, lookup))
    })

    Await.result(Future.sequence(futures), Duration.Inf).flatten.toSet
  }

  private def computeNonRecursiveRules(ac: AliasingConstraint): Unit = {
    for (pred <- sid.predicates.values;
         rule <- pred.rules if !rule.isRecursive) {
      val newTypes = ptypesIterationParallel(ac, pred, (p, a) => stateGet(p.name, a), ruleFilter = !_.isRecursive)
      if (!state.contains(pred.name)) state.put(pred.name, mutable.Map.empty)
      state(pred.name).put(ac, mutable.Set.from(newTypes))

      if (pred.rules.forall(!_.isRecursive))
        finished.add((pred.name, ac))
    }
  }

  class Elem(val it: Int, val ac: AliasingConstraint, val pred: Predicate[SymbolicHeapBtw]) extends Ordered[Elem] {

    override def toString: String = it + " " + ac + " " + pred

    override def compare(that: Elem): Int = that.it - it
  }


  /**
    * DOES NOT WORK
    */
  private def unfold(acc: AliasingConstraint): Unit = {

    computeNonRecursiveRules(acc)

    val toRemove: mutable.Map[(String, AliasingConstraint), Int] = mutable.Map.empty

    val pq: mutable.PriorityQueue[Elem] = mutable.PriorityQueue.empty

    sid.predicates.values.foreach { pred =>
      if (!finished.contains((pred.name, acc)))
        pq.enqueue(new Elem(iterations.getOrElse((pred.name, acc), 0), acc, pred))
    }

    //    val queue: mutable.Queue[(AliasingConstraint, SymbolicHeapBtw)] = mutable.Queue(recursiveRules.map((ac, _)))
    //queue.clear()
    //queue.appendAll(sid.predicates.values.map((ac, _)))
    while (pq.nonEmpty) {
      println("=======")
      pq.foreach(println)

      val elem = pq.dequeue()

      queue.clear()
      val newTypes = ptypesIterationParallel(elem.ac, elem.pred, (p, a) => stateGet(p.name, a), _.isRecursive)
      iterations.updateWith((elem.pred.name, elem.ac)) { case Some(value) => Some(value + 1)
      case None => Some(0)
      }

      queue.foreach { case (constraint, value) =>
        pq.enqueue(new Elem(iterations.getOrElse((value.name, constraint), 0), constraint, value))
      }

      if (!state.contains(elem.pred.name)) state.put(elem.pred.name, mutable.Map.empty)

      if (state(elem.pred.name).contains(elem.ac)) {
        val prevSize = state(elem.pred.name)(elem.ac).size
        state(elem.pred.name)(elem.ac).addAll(newTypes)

        val newSize = state(elem.pred.name)(elem.ac).size

        if (newSize == prevSize && queue.isEmpty) {
          finished.add((elem.pred.name, elem.ac))
        }
        else {
          pq.enqueue(new Elem(elem.it + 1, elem.ac, elem.pred))
        }
      } else {
        state(elem.pred.name).put(elem.ac, mutable.Set.from(newTypes))
        pq.enqueue(new Elem(elem.it + 1, elem.ac, elem.pred))
      }
    }
  }

  private def unfold(): Unit = {

    val xSubs = x.subsets().filter(_.nonEmpty).toSeq
    val allAcs = sid.predicates.values.flatMap(pred => xSubs.flatMap(xx => AliasingConstraint.allAliasingConstraints(pred.freeVars.union(xx)))).toSeq

    for (ac <- allAcs) {
      computeNonRecursiveRules(ac)
    }

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

        val iteration = sid.predicates.values.filter(pred => pred.rules.exists(_.isRecursive)).map(pred => (pred, ptypesIterationParallel(ac, pred, (p, a) => stateGet(p.name, a), ruleFilter = _.isRecursive)))
        for ((pred, newTypes) <- iteration) {
          if (!state.contains(pred.name)) state.put(pred.name, mutable.Map.empty)

          if (state(pred.name).contains(ac)) {
            val prevSize = state(pred.name)(ac).size
            state(pred.name)(ac).addAll(newTypes)

            val newSize = state(pred.name)(ac).size

            if (newSize != prevSize) changed = true
          } else {
            state(pred.name).put(ac, mutable.Set.from(newTypes))
            changed = true
          }
        }
      }
    }

    allFinished = true
  }
}
