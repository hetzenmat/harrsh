package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.{Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.GSL.projections.prototype.{StackForestProjection, TreeProjection}
import at.forsyte.harrsh.GSL.query.QueryContext.getSid
import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, NullConst, Var}

import scala.collection.SortedSet
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}

/**
  * Created by Matthias Hetzenberger on 2021-02-13
  */
class PhiType private(val projections: SortedSet[StackForestProjection]) extends Ordered[PhiType] {

  lazy val alloced: collection.Set[Var] = projections.unsorted.
                                          flatMap(_.formula)
                                          .map(tp => TreeProjection.getRootPred(tp))
                                          .map(call => call.getRootArgument(getSid))

  lazy val freeVars: SortedSet[Var] = projections.flatMap(_.freeVars)

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint[Var]): PhiType = {
    PhiType.rename(x, y, ac, Set(this)).head
  }

  def forget(ac: AliasingConstraint[Var], x: FreeVar): Option[PhiType] = {
    PhiType.from(projections.map(_.forget(ac, x)).filter(_.isDelimited()), ac)
  }

  def extend(x: FreeVar, ac: AliasingConstraint[Var]): Option[PhiType] = {
    PhiType.from(projections ++ projections.flatMap(_.extend(x)), ac)
  }

  def extend(ac: AliasingConstraint[Var], acSup: AliasingConstraint[Var]): PhiType = {
    PhiType.extend(ac, acSup, Set(this), getSid).head
  }

  override def compare(that: PhiType): Int = {
    scala.Ordering.Implicits.sortedSetOrdering[SortedSet, StackForestProjection].compare(this.projections, that.projections)
  }

  def substitute(subst: Substitution[Var]): PhiType = new PhiType(SortedSet.from(projections.map(_.substitute(subst))))

  override def equals(obj: Any): Boolean = obj match {
    case v: PhiType => v.projections == projections
  }

  override def hashCode: Int = projections.hashCode()

  override def toString: String = projections.toString()
}

object PhiType {

  def unapply(t: PhiType): Option[SortedSet[StackForestProjection]] = Some(t.projections)

  def from(it: Iterable[StackForestProjection], ac: AliasingConstraint[Var]): Option[PhiType] = {

    Utils.debugRequire(it.forall(_.isDelimited()))

    if (it.isEmpty /*|| it.exists(!_.isDelimited(sid))*/ ) {
      // TODO: Really return None if empty?
      None
    } else {
      Some(new PhiType(SortedSet.from(it.flatMap(_.impliedSet))))
    }
  }

  def empty: PhiType = new PhiType(SortedSet.from(Seq(StackForestProjection.empty)))

  def composition(left: PhiType, right: PhiType, ac: AliasingConstraint[Var]): Option[PhiType] = {
    Utils.debugRequire(Utils.isCanonical(left, ac))
    Utils.debugRequire(Utils.isCanonical(right, ac))

    if ((left.alloced intersect right.alloced).isEmpty) {

      val projections = for (phi1 <- left.projections.unsorted;
                             phi2 <- right.projections.unsorted) yield {
        StackForestProjection.composition(phi1, phi2)
      }

      PhiType.from(projections.flatten.filter(_.isDelimited()), ac)
    } else {
      None
    }
  }

  def composition(left: Iterable[PhiType], right: Iterable[PhiType], ac: AliasingConstraint[Var]): Iterable[PhiType] = {

    val futures: Iterable[Future[Option[PhiType]]] =
      for (l <- left;
           r <- right) yield Future {
        composition(l, r, ac)
      }

    Await.result(Future.sequence(futures), Duration.Inf).flatten

    //    (for (l <- left;
    //          r <- right) yield composition(sid, l, r, ac)).flatten
  }

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint[Var], types: Iterable[PhiType]): Iterable[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet[Var].subsetOf(ac.domain))

    val yMax = y.map(v => ac.largestAlias(v))
    val subst: Substitution[Var] = Substitution.from(x.zip(yMax))
    types.flatMap(t => PhiType.from(t.projections.map(_.substitute(subst)), ac))
  }

  def forget(ac: AliasingConstraint[Var], x: FreeVar, types: Iterable[PhiType]): Iterable[PhiType] = types.flatMap(_.forget(ac, x))

  def extend(x: FreeVar, types: Iterable[PhiType], ac: AliasingConstraint[Var]): Iterable[PhiType] = types.flatMap(_.extend(x, ac)) // TODO order x ac

  def extend(ac: AliasingConstraint[Var], acSup: AliasingConstraint[Var], types: Iterable[PhiType], sid: SID_btw): Iterable[PhiType] = {
    require(ac.subsetOf(acSup))

    val y = ac.partition.map(_.max)
    val yReplaced = y.map(v => acSup.largestAlias(v))
    val subst: Substitution[Var] = Substitution.from(y.zip(yReplaced))

    // TODO: Recheck definition
    val z = acSup.partition.map(_.max).filter(z_ => ac.domain.forall(y => acSup =/= (y, z_))).asInstanceOf[IndexedSeq[FreeVar]]

    if (ac.partition.size != acSup.partition.size && types.nonEmpty) {
      print("")
    }

    val r = types.flatMap({ case PhiType(projections) =>
      def aux: Int => Option[PhiType] = {
        case 0 => PhiType.from(projections.map(_.substitute(subst)), acSup)
        case n => aux(n - 1) match {
          case Some(value) => value.extend(z(n - 1), acSup)
          case None => None
        }
      }

      aux(z.length)
    })

    r
  }

  /**
    * Semantic way of computing pointer models instead of iterating over all assignments to {0, ..., n}
    *
    * Should be equivalent to the exhaustive way
    *
    * TODO: Adapt to overload
    */
    def ptrmodel2(sid: SID_btw, ac: AliasingConstraint[Var], pointsTo: PointsTo): PhiType = {

    val partitions: Seq[Var] = pointsTo.vars.map(v => ac.largestAlias(v)).incl(NullConst).toSeq.sorted

      val projections = (for (pred <- sid.predicates.values;
                              rule <- pred.rules if rule.pointsTo.to.size == pointsTo.to.size) yield {

      val replacement: Option[Map[Var, Var]] = rule.pointsTo.varSeq.zip(pointsTo.varSeq.map(v => ac.largestAlias(v))).foldLeft(Some(Map.empty): Option[Map[Var, Var]])({
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
              val subst: Substitution[Var] = Substitution.from(replacement)

              universals.foreach { v =>
                subst.add(v, univSubst(univAC.largestAlias(v)))
              }

              def ruleSatisfiable(subst: Substitution[Var]): Boolean = {
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

                val tp = TreeProjection(rule.calls.map(_.substitute(subst)).sorted,
                                        PredicateCall(pred.name, pred.args.map(FreeVar).map(subst.apply)))

                if (!ruleSatisfiable(subst)) Seq()
                else Seq(Some(new StackForestProjection(SortedSet.empty,
                                                        SortedSet.from(bv.take(univVars.size)),
                                                        Seq(tp))))
              } else {
                (for (assignment <- Utils.allAssignments(toAssign.toSeq.sorted, partitions)) yield {

                  val substAll = subst.clone()
                  substAll.addAll(assignment)

                  val tp = TreeProjection(rule.calls.map(_.substitute(substAll)).sorted,
                                          PredicateCall(pred.name, pred.args.map(FreeVar).map(substAll.apply)))

                  if (!ruleSatisfiable(substAll)) None
                  else Some(new StackForestProjection(SortedSet.empty,
                                                      SortedSet.from(bv.take(univVars.size)),
                                                      Seq(tp)))
                }): Seq[Option[StackForestProjection]]
              }
            }).flatten.flatten.toSet: Set[StackForestProjection]
          }: Option[Set[StackForestProjection]]
        }

        result
      }).flatten.flatten.toSet

      PhiType.from(projections.filter(_.isDelimited()), ac).get
    }

  def ptrmodel(ac: AliasingConstraint[Var], pointsTo: PointsTo): PhiType = {

    val pm = pointsTo.ptrmodel(ac.restricted(pointsTo.vars.incl(NullConst)))

    val k = getSid.predicates.values.map(_.args.length).max

    val R = getSid.allRuleInstancesForPointsTo(pm(pointsTo.from), pointsTo.to.map(pm), 0 to ac.domain.size + k)

    val types = R.map({
      case (_, instance) => StackForestProjection.fromPtrmodel(ac, instance, pm, pointsTo)
    }).filter(_.isDelimited())

    val r = PhiType.from(types, ac)

    //    val _2 = ptrmodel2(getSid, ac, pointsTo)
    //
    //    if (_2 != r.get) {
    //      require(false)
    //    }

    r.get
  }
}