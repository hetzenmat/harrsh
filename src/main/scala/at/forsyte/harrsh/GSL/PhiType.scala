package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.PointsTo
import at.forsyte.harrsh.seplog.{FreeVar, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-13
  */
case class PhiType(projections: Set[StackForestProjection]) {
  def alloced(sid: SID_btw): Set[FreeVar] = projections.
                                            flatMap(_.formula)
                                            .map(_.rootpred)
                                            .map(c => c.args(sid.predicates(c.pred).predrootIndex)).asInstanceOf[Set[FreeVar]]

  def freeVars: Set[FreeVar] = projections.flatMap(_.freeVars)

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint): PhiType = {
    PhiType.rename(x, y, ac, Set(this)).head
  }

  def forget(sid: SID_btw, ac: AliasingConstraint, x: FreeVar): PhiType = {
    PhiType(projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)))
  }

  def extend(x: FreeVar): PhiType = {
    PhiType(projections ++ projections.flatMap(_.extend(x)))
  }

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint): PhiType = {
    PhiType.extend(ac, acSup, Set(this)).head
  }
}

object PhiType {

  def empty: PhiType = PhiType(Set.empty)

  def composition(sid: SID_btw, left: PhiType, right: PhiType): Option[PhiType] = {
    if ((left.alloced(sid) intersect right.alloced(sid)).isEmpty) {
      val projections = for (phi1 <- left.projections;
                             phi2 <- right.projections) yield StackForestProjection.composition(phi1, phi2)
      Some(PhiType(projections.flatten.filter(_.isDelimited(sid))))
    } else {
      None
    }
  }

  def composition(sid: SID_btw, left: Iterable[PhiType], right: Iterable[PhiType]): Iterable[PhiType] =
    (for (l <- left;
          r <- right) yield composition(sid, l, r)).flatten

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint, types: Iterable[PhiType]): Iterable[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet[Var].subsetOf(ac.domain))

    val yMax = y.map(ac.largestAlias)
    val subst: Map[Var, Var] = x.zip(yMax).toMap
    types.map(t => PhiType(t.projections.map(_.substitute(subst))))
  }

  def forget(sid: SID_btw, ac: AliasingConstraint, x: FreeVar, types: Iterable[PhiType]): Iterable[PhiType] = types.map(_.forget(sid, ac, x))

  def extend(x: FreeVar, types: Iterable[PhiType]): Iterable[PhiType] = types.map(_.extend(x))

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint, types: Iterable[PhiType]): Iterable[PhiType] = {
    require(ac.subsetOf(acSup))

    val y = ac.partition.map(_.max)
    val yReplaced = y.map(acSup.largestAlias)
    val subst: Map[Var, Var] = y.zip(yReplaced).toMap

    // TODO: Recheck definition
    val z = acSup.partition.map(_.max).filter(z_ => ac.domain.forall(y => acSup =/= (y, z_))).asInstanceOf[Seq[FreeVar]]

    types.map({ case PhiType(projections) =>
      def aux: Int => PhiType = {
        case 0 => PhiType(projections.map(_.substitute(subst)))
        case n => aux(n - 1).extend(z(n - 1))
      }

      aux(z.length)
    })
  }

  def ptrmodel(sid: SID_btw, ac: AliasingConstraint, pointsTo: PointsTo): PhiType = {

    val pm = pointsTo.ptrmodel(ac)

    val R = sid.allRuleInstancesForPointsTo(pm(pointsTo.from), pointsTo.to.map(pm), 0 to ac.domain.size)

    val r = PhiType(R.map({ case (_, instance) => StackForestProjection.fromPtrmodel(ac, instance, pm) }).filter(_.isDelimited(sid)).toSet)

    r
  }
}