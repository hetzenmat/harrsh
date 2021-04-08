package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.{Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

import scala.collection.SortedSet
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}

/**
  * Created by Matthias Hetzenberger on 2021-02-13
  */
case class PhiType private(projections: SortedSet[StackForestProjection]) extends Ordered[PhiType] {

  def alloced(sid: SID_btw): Set[FreeVar] = projections.unsorted.
                                                       flatMap(_.formula)
                                                       .map(_.rootpred)
                                                       .map(c => c.args(sid.predicates(c.pred).predrootIndex)).asInstanceOf[Set[FreeVar]]

  def freeVars: SortedSet[FreeVar] = projections.flatMap(_.freeVars)

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint[Var], sid: SID_btw): PhiType = {
    PhiType.rename(x, y, ac, Set(this), sid).head
  }

  def forget(ac: AliasingConstraint[Var], x: FreeVar, sid: SID_btw): Option[PhiType] = {
    PhiType.from(projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)), sid, ac)
  }

  def extend(x: FreeVar, sid: SID_btw, ac: AliasingConstraint[Var]): Option[PhiType] = {
    PhiType.from(projections ++ projections.flatMap(_.extend(x)), sid, ac)
  }

  def extend(ac: AliasingConstraint[Var], acSup: AliasingConstraint[Var], sid: SID_btw): PhiType = {
    PhiType.extend(ac, acSup, Set(this), sid).head
  }

  override def compare(that: PhiType): Int = {
    scala.Ordering.Implicits.sortedSetOrdering[SortedSet, StackForestProjection].compare(this.projections, that.projections)
  }

  def substitute(subst: Map[Var, Var]): PhiType = PhiType(SortedSet.from(projections.map(_.substitute(subst))))

}

object PhiType {

  def from(it: Iterable[StackForestProjection], sid: SID_btw, ac: AliasingConstraint[Var]): Option[PhiType] = {

    Utils.debugRequire(it.forall(_.isDelimited(sid)))


    if (it.isEmpty /*|| it.exists(!_.isDelimited(sid))*/ ) {
      // TODO: Really return None if empty?
      None
    } else {
      Some(PhiType(SortedSet.from(it.flatMap(_.impliedSet(sid)))))
    }
  }

  def empty: PhiType = PhiType(SortedSet.from(Seq(StackForestProjection.empty)))

  def composition(sid: SID_btw, left: PhiType, right: PhiType, ac: AliasingConstraint[Var]): Option[PhiType] = {
    Utils.debugRequire(Utils.isCanonical(left, ac))
    Utils.debugRequire(Utils.isCanonical(right, ac))

    if ((left.alloced(sid) intersect right.alloced(sid)).isEmpty) {

      // TODO: parallel
      val projections = for (phi1 <- left.projections.unsorted;
                             phi2 <- right.projections.unsorted) yield StackForestProjection.composition(phi1, phi2, sid)
      PhiType.from(projections.flatten.filter(_.isDelimited(sid)), sid, ac)
    } else {
      None
    }
  }

  def composition(sid: SID_btw, left: Iterable[PhiType], right: Iterable[PhiType], ac: AliasingConstraint[Var]): Iterable[PhiType] = {

    val futures: Iterable[Future[Option[PhiType]]] =
      for (l <- left;
           r <- right) yield Future {
        composition(sid, l, r, ac)
      }

    Await.result(Future.sequence(futures), Duration.Inf).flatten

    //    (for (l <- left;
    //          r <- right) yield composition(sid, l, r, ac)).flatten
  }

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint[Var], types: Iterable[PhiType], sid: SID_btw): Iterable[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet[Var].subsetOf(ac.domain))

    val yMax = y.map(v => AliasingConstraint.largestAlias(ac, v))
    val subst: Map[Var, Var] = x.zip(yMax).toMap
    types.flatMap(t => PhiType.from(t.projections.map(_.substitute(subst)), sid, ac))
  }

  def forget(sid: SID_btw, ac: AliasingConstraint[Var], x: FreeVar, types: Iterable[PhiType]): Iterable[PhiType] = types.flatMap(_.forget(ac, x, sid))

  def extend(x: FreeVar, types: Iterable[PhiType], sid: SID_btw, ac: AliasingConstraint[Var]): Iterable[PhiType] = types.flatMap(_.extend(x, sid, ac))

  def extend(ac: AliasingConstraint[Var], acSup: AliasingConstraint[Var], types: Iterable[PhiType], sid: SID_btw): Iterable[PhiType] = {
    require(ac.subsetOf(acSup))

    val y = ac.partition.map(_.max)
    val yReplaced = y.map(v => AliasingConstraint.largestAlias(acSup, v))
    val subst: Map[Var, Var] = y.zip(yReplaced).toMap

    // TODO: Recheck definition
    val z = acSup.partition.map(_.max).filter(z_ => ac.domain.forall(y => acSup =/= (y, z_))).asInstanceOf[Seq[FreeVar]]

    if (ac.partition.size != acSup.partition.size && types.nonEmpty) {
      print("")
    }

    val r = types.flatMap({ case PhiType(projections) =>
      def aux: Int => Option[PhiType] = {
        case 0 => PhiType.from(projections.map(_.substitute(subst)), sid, acSup)
        case n => aux(n - 1) match {
          case Some(value) => value.extend(z(n - 1), sid, acSup)
          case None => None
        }
      }

      aux(z.length)
    })

    r
  }

  def ptrmodel2(sid: SID_btw, ac: AliasingConstraint[Var], pointsTo: PointsTo): PhiType = {

    val partitions: Seq[Var] = pointsTo.vars.map(v => AliasingConstraint.largestAlias(ac, v)).incl(NullConst).toSeq.sorted

    val projections = (for (pred <- sid.predicates.values;
                            rule <- pred.rules if rule.pointsTo.to.size == pointsTo.to.size) yield {

      val replacement: Option[Map[Var, Var]] = rule.pointsTo.varSeq.zip(pointsTo.varSeq.map(v => AliasingConstraint.largestAlias(ac, v))).foldLeft(Some(Map.empty): Option[Map[Var, Var]])({
        case (None, _) => None
        case (Some(m), (l, r)) =>
          if (l == NullConst && r != NullConst) None
          else if (m.contains(l) && m(l) != r) None
          else Some(m.updated(l, r))
      })

      val result: Option[Set[StackForestProjection]] = replacement match {
        case None => None
        case Some(replacement) => Some {
          val otherVars: Set[Var] = rule.allVars.diff(rule.pointsTo.vars)

          (for (universals <- otherVars.subsets();
                univAC <- AliasingConstraint.allAliasingConstraints(universals)) yield {
            val toAssign = otherVars.diff(universals)

            val bv = LazyList.from(1).map(BoundVar.apply)
            val univVars = univAC.partition.map(_.max)
            val univSubst: Map[Var, Var] = univVars.sorted.zip(bv).toMap
            val subst: Map[Var, Var] = universals.toSeq.sorted.map(v => (v, univSubst(AliasingConstraint.largestAlias(univAC, v)))).foldLeft(replacement)({
              case (map, (v1, v2)) =>
                require(!map.contains(v1))

                map.updated(v1, v2)
            })

            def ruleSatisfiable(subst: Map[Var, Var]): Boolean = {
              def eqHolds(eq: Equality): Boolean = (subst(eq.left), subst(eq.right)) match {
                case (l: BoundVar, r: BoundVar) => l == r
                case (l: FreeVar, r: FreeVar) => l == r
                case (NullConst, NullConst) => true
                case _ => false
              }

              val eqsHold = rule.equalities.forall(eqHolds)
              val disEqsHold = rule.disEqualities.map(_.toEquality).forall(eq => !eqHolds(eq))

              eqsHold && disEqsHold
            }

            if (toAssign.isEmpty) {


              val tp = TreeProjection(rule.calls.map(_.substitute(subst)),
                                      PredicateCall(pred.name, pred.args.map(FreeVar).map(subst)))

              if (tp.hasNullAsRoot(sid) || !ruleSatisfiable(subst)) Seq()
              else Seq(Some(new StackForestProjection(SortedSet.empty,
                                                      SortedSet.from(bv.take(univVars.size)),
                                                      SortedSet.from(Seq(tp)))))
            } else {
              (for (assignment <- Utils.allAssignments(toAssign.toSeq.sorted, partitions)) yield {
                val substAll: Map[Var, Var] = assignment.foldLeft(subst)({
                  case (map, (v1, v2)) =>
                    require(!map.contains(v1))

                    map.updated(v1, v2)
                })

                val tp = TreeProjection(rule.calls.map(_.substitute(substAll)),
                                        PredicateCall(pred.name, pred.args.map(FreeVar).map(substAll)))

                if (tp.hasNullAsRoot(sid) || !ruleSatisfiable(substAll)) None
                else Some(new StackForestProjection(SortedSet.empty,
                                                    SortedSet.from(bv.take(univVars.size)),
                                                    SortedSet.from(Seq(tp))))
              }): Seq[Option[StackForestProjection]]
            }
          }).flatten.flatten.toSet: Set[StackForestProjection]
        }: Option[Set[StackForestProjection]]
      }

      result
    }).flatten.flatten.toSet

    PhiType.from(projections, sid, ac).get
  }

  def ptrmodel(sid: SID_btw, ac: AliasingConstraint[Var], pointsTo: PointsTo): PhiType = {

    val pm = pointsTo.ptrmodel(ac.restricted(pointsTo.vars.incl(NullConst)))

    val k = sid.predicates.values.map(_.args.length).max

    val R = sid.allRuleInstancesForPointsTo(pm(pointsTo.from), pointsTo.to.map(pm), 0 to ac.domain.size + k)

    val types = R.map({
      case (_, instance) => StackForestProjection.fromPtrmodel(ac, instance, pm, pointsTo)
    }).filter(_.isDelimited(sid))

    val r = PhiType.from(types, sid, ac)

    if (r.get.projections.exists(p => p.guardedUniversals.nonEmpty) || r.get.projections.exists(_.guardedExistentials.nonEmpty)) {
      print("")
    }

    val _2 = ptrmodel2(sid, ac, pointsTo)

    if (_2 != r.get) {
      print()
    }

    r.get
  }
}