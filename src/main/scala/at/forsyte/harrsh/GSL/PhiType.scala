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

  def rename(x: Seq[Var], y: Seq[Var], ac: AliasingConstraint): Option[PhiType] = {
    if (x.length == y.length && x.length == x.toSet.size && y.toSet.subsetOf(ac.domain)) {
      val yMax = y.map(ac.largestAlias)
      val subst = x.zip(yMax).toMap
      Some(PhiType(sid, projections.map(_.substitute(subst))))
    } else {
      None
    }
  }

  def forget(ac: AliasingConstraint, x: FreeVar): PhiType = {
    PhiType(sid, projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)))
  }
}

object PhiType {
  def composition(left: PhiType, right: PhiType): Option[PhiType] = {
    if (left.sid == right.sid && (left.alloced intersect right.alloced).isEmpty) {
      val projections = for (phi1 <- left.projections;
                             phi2 <- right.projections) yield StackForestProjection.composition(phi1, phi2)
      Some(PhiType(left.sid, projections.flatten.filter(_.isDelimited(left.sid))))
    } else {
      None
    }
  }
}
