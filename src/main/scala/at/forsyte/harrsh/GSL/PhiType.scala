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

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint): PhiType = {
    PhiType.rename(x, y, ac, Set(this)).head
  }

  def forget(ac: AliasingConstraint, x: FreeVar): PhiType = {
    PhiType(sid, projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)))
  }

  def extend(x: FreeVar): PhiType = {
    PhiType(sid, projections union projections.flatMap(_.extend(x)))
  }

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint): PhiType = {
    PhiType.extend(ac, acSup, Set(this)).head
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

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint, types: Set[PhiType]): Set[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet.subsetOf(ac.domain))

    val yMax = y.map(ac.largestAlias)
    val subst: Map[Var, Var] = x.zip(yMax).toMap
    types.map(t => PhiType(t.sid, t.projections.map(_.substitute(subst))))
  }

  def forget(ac: AliasingConstraint, x: FreeVar, types: Set[PhiType]): Set[PhiType] = types.map(_.forget(ac, x))

  def extend(x: FreeVar, types: Set[PhiType]): Set[PhiType] = types.map(_.extend(x))

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint, types: Set[PhiType]): Set[PhiType] = {
    require(ac.subsetOf(acSup))

    val y = ac.partition.map(_.max)
    val yReplaced = y.map(acSup.largestAlias)
    val subst: Map[Var, Var] = y.zip(yReplaced).toMap

    // TODO: Recheck definition
    val z: Seq[FreeVar] = acSup.partition.map(_.max).filterNot(ac.domain)

    types.map({ case PhiType(sid, projections) =>
      def aux: Int => PhiType = {
        case 0 => PhiType(sid, projections.map(_.substitute(subst)))
        case n => aux(n - 1).extend(z(n - 1))
      }

      aux(z.length)
    })
  }
}