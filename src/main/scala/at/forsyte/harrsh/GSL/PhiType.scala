package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.{PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}

import scala.collection.SortedSet

/**
  * Created by Matthias Hetzenberger on 2021-02-13
  */
case class PhiType private(projections: SortedSet[StackForestProjection]) extends Ordered[PhiType] {

  def alloced(sid: SID_btw): Set[FreeVar] = projections.unsorted.
                                                       flatMap(_.formula)
                                                       .map(_.rootpred)
                                                       .map(c => c.args(sid.predicates(c.pred).predrootIndex)).asInstanceOf[Set[FreeVar]]

  def filterDUSH(sid: SID_btw, ac: AliasingConstraint): PhiType = {
    println()
    PhiType.from(projections.unsorted.filter(_.isDUSH(sid)), sid, ac).get
  }

  def freeVars: SortedSet[FreeVar] = projections.flatMap(_.freeVars)

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint, sid: SID_btw): PhiType = {
    PhiType.rename(x, y, ac, Set(this), sid).head
  }

  def forget(ac: AliasingConstraint, x: FreeVar, sid: SID_btw): Option[PhiType] = {
    PhiType.from(projections.map(_.forget(ac, x)).filter(_.isDelimited(sid)), sid, ac)
  }

  def extend(x: FreeVar, sid: SID_btw, ac: AliasingConstraint): Option[PhiType] = {
    PhiType.from(projections ++ projections.flatMap(_.extend(x)), sid, ac)
  }

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint, sid: SID_btw): PhiType = {
    PhiType.extend(ac, acSup, Set(this), sid).head
  }

  override def compare(that: PhiType): Int = {
    scala.Ordering.Implicits.sortedSetOrdering[SortedSet, StackForestProjection].compare(this.projections, that.projections)
  }

  def substitute(subst: Map[Var, Var]): PhiType = PhiType(SortedSet.from(projections.map(_.substitute(subst))))

}

object PhiType {

  def from(it: Iterable[StackForestProjection], sid: SID_btw, ac: AliasingConstraint): Option[PhiType] = {

    /*val itSubst = it.map(sf => {
      val subst: Map[Var, Var] = sf.freeVars.map(v => (v, ac.largestAlias(v))).toMap
      sf.substitute(subst)
    })*/

    def prop(sf: StackForestProjection): Boolean = {
      val vars = sf.formula.unsorted.map(_.rootpred).map({ case PredicateCall(pred, args) =>
        val p = sid.predicates(pred)
        args(p.predrootIndex)
      }).toSet

      vars.size < sf.formula.size
    }

    def unsat(sf: StackForestProjection): Boolean = {
      val su: Map[Var, Var] = sf.freeVars.map(v => (v, ac.largestAlias(v))).toMap
      val sf2 = sf.substitute(su)

      prop(sf2)
    }

    //val itt = it.filterNot(prop)

//    if (Utils.nonCanonicalSF(it, ac)) {
//      println("largest")
//    }

    if (it.exists(unsat)) {
      println("unsat")
    }

    if (it.exists(prop)) {
      println("here")
      //      // TODO Completeness?
      //      None
    }

    //val it2 = it.filter(sf => sf.formula.forall(tp => !tp.allholepreds.contains(tp.rootpred)))

    if (it.isEmpty) {
      print("")
    }

    if (it.exists(!_.isDelimited(sid))) {
      ???
    }

    if (it.isEmpty /*|| it.exists(!_.isDelimited(sid))*/) {
      // TODO: Really return None if empty?
      None
    } else {
//      val closure = it.flatMap(f => StackForestProjection.composition(f, new StackForestProjection(SortedSet.empty,
//                                                                                                   SortedSet.empty,
//                                                                                                   SortedSet.empty,
//                                                                                                   Empty), sid))
//                      .filter(_.isDelimited(sid))
      val closure = it.flatMap(_.impliedSet(sid)).filter(_.isDelimited(sid))
      Some(PhiType(SortedSet.from(closure)))
    }
  }

  def empty: PhiType = PhiType(SortedSet.from(Seq(new StackForestProjection(SortedSet.empty,
                                                                            SortedSet.empty,
                                                                            SortedSet.empty,
                                                                            Empty))))

  def composition(sid: SID_btw, left: PhiType, right: PhiType, ac: AliasingConstraint): Option[PhiType] = {
    if (Utils.nonCanonical(left, ac) || Utils.nonCanonical(right, ac)) {
      println("sdf")
    }
    if ((left.alloced(sid) /*.map(v => ac.largestAlias(v))*/ intersect right.alloced(sid)).isEmpty) {

      val projections = for (phi1 <- left.projections.unsorted;
                             phi2 <- right.projections.unsorted) yield StackForestProjection.composition(phi1, phi2, sid)
      PhiType.from(projections.flatten.filter(_.isDelimited(sid)), sid, ac)
    } else {
      None
    }
  }

  def composition(sid: SID_btw, left: Iterable[PhiType], right: Iterable[PhiType], ac: AliasingConstraint): Iterable[PhiType] =
    (for (l <- left;
          r <- right) yield composition(sid, l, r, ac)).flatten

  def rename(x: Seq[FreeVar], y: Seq[FreeVar], ac: AliasingConstraint, types: Iterable[PhiType], sid: SID_btw): Iterable[PhiType] = {
    require(x.length == y.length)
    require(x.length == x.toSet.size)
    require(y.toSet[Var].subsetOf(ac.domain))

    val yMax = y.map(ac.largestAlias)
    val subst: Map[Var, Var] = x.zip(yMax).toMap
    types.flatMap(t => PhiType.from(t.projections.map(_.substitute(subst)), sid, ac))
  }

  def forget(sid: SID_btw, ac: AliasingConstraint, x: FreeVar, types: Iterable[PhiType]): Iterable[PhiType] = types.flatMap(_.forget(ac, x, sid))

  def extend(x: FreeVar, types: Iterable[PhiType], sid: SID_btw, ac: AliasingConstraint): Iterable[PhiType] = types.flatMap(_.extend(x, sid, ac))

  def extend(ac: AliasingConstraint, acSup: AliasingConstraint, types: Iterable[PhiType], sid: SID_btw): Iterable[PhiType] = {
    require(ac.subsetOf(acSup))

    val y = ac.partition.map(_.max)
    val yReplaced = y.map(acSup.largestAlias)
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

  def ptrmodel(sid: SID_btw, ac: AliasingConstraint, pointsTo: PointsTo): PhiType = {

    val pm = pointsTo.ptrmodel(ac.restricted(pointsTo.vars.incl(NullConst)))

    val k = sid.predicates.values.map(_.args.length).max

    val R = sid.allRuleInstancesForPointsTo(pm(pointsTo.from), pointsTo.to.map(pm), 0 to ac.domain.size + k)

    val r = PhiType.from(R.map({ case (_, instance) => StackForestProjection.fromPtrmodel(ac, instance, pm, pointsTo) }).filter(_.isDelimited(sid)), sid, ac)

    r.get
  }
}