package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{FreeVar, Var}

/**
  * Created by Matthias Hetzenberger on 2021-02-13
  */
case class PhiType(sid: SID, projections: Set[StackForestProjection]) {
  def alloced: Set[FreeVar] = projections.flatMap(_.formula
                                                   .map(_.rootpred.pred)
                                                   .map(sid.predicates)
                                                   .map(_.predroot))

  def freeVars: Set[FreeVar] = projections.flatMap(_.freeVars)

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint): PhiType = {
    PhiType.rename(x, y, ac, Set(this)).head
  }

  def forget(ac: AliasingConstraint, x: FreeVar): PhiType = {
    PhiType(sid, projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)))
  }

  def extend(x: FreeVar): PhiType = {
    PhiType(sid, projections union projections.flatMap(_.extend(x)))
  }
}

object PhiType {
  def composition(left: PhiType, right: PhiType): Option[PhiType] =
    if (left.sid == right.sid && (left.alloced intersect right.alloced).isEmpty) {
      val projections = for (phi1 <- left.projections;
                             phi2 <- right.projections) yield StackForestProjection.composition(phi1, phi2)
      Some(PhiType(left.sid, projections.flatten.filter(_.isDelimited(left.sid))))
    } else {
      None
    }

  def composition(left: Set[PhiType], right: Set[PhiType]): Set[PhiType] =
    (for (l <- left;
          r <- right) yield composition(l, r)).flatten

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint, types: Set[PhiType]): Set[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet.subsetOf(ac.domain))

    val yMax = y.map(ac.largestAlias)
    val subst = x.zip(yMax).toMap
    types.map(t => PhiType(t.sid, t.projections.map(_.substitute(subst))))
  }

  def forget(ac: AliasingConstraint, x: FreeVar, types: Set[PhiType]): Set[PhiType] = types.map(_.forget(ac, x))

  def extend(x: FreeVar, types: Set[PhiType]): Set[PhiType] = types.map(_.extend(x))
}