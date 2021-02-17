package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}

import scala.annotation.tailrec
import scala.collection.mutable

object TypeComputation {

  type PredTypes = (SID.Predicate[SymbolicHeap], AliasingConstraint) => Set[PhiType]
  type PredTypesMap = Map[(SID.Predicate[SymbolicHeap], AliasingConstraint), Set[PhiType]]

  def ptypes(sid: SID, x: Set[Var], atom: Atom, ac: AliasingConstraint): Iterable[PhiType] = atom match {
    case e: Equality => types(sid, e, ac)
    case d: DisEquality => types(sid, d, ac)
    case p: PointsTo => types(sid, p, ac)
    case PredicateCall(predName, args) =>
      val pred = sid.predicates(predName)

      val parameters = pred.args.map(FreeVar)

      val acExtended = ac.reverseRenaming(parameters, args)
      val acExtendedRestricted = acExtended.restricted(x.union(parameters.toSet))

      val types = FixedPoint(pred, acExtendedRestricted)
      val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(ac, acExtended, typesRenamed)

      typesExtended
  }

  def ptypes(sid: SID, x: Set[Var], atoms: Seq[Atom], ac: AliasingConstraint): Iterable[PhiType] = atoms match {
    case atom +: Seq() => ptypes(sid, x, atom, ac)
    case head +: rest => PhiType.composition(sid, ptypes(sid, x, head, ac), ptypes(sid, x, rest, ac))
  }

  def ptypes(sid: SID, x: Set[Var], sh: SymbolicHeap, ac: AliasingConstraint): Iterable[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(x.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sid, x, sh.dropFirstQuantifiedVar(fresh), ac_)
        PhiType.forget(sid, ac_, fresh, types)
      })
    } else ptypes(sid, x, sh.atoms, ac)

  sealed trait Quantifier {
    def test[A](coll: Iterable[A], p: A => Boolean): Boolean
  }

  case object Exists extends Quantifier {
    override def test[A](coll: Iterable[A], p: A => Boolean): Boolean = coll.exists(p)
  }

  case object Forall extends Quantifier {
    override def test[A](coll: Iterable[A], p: A => Boolean): Boolean = coll.forall(p)
  }

  private def magicWandSeptractionHelper(q: Quantifier,
                                         sid: SID,
                                         ac: AliasingConstraint,
                                         guard: GslFormula,
                                         left: GslFormula,
                                         right: GslFormula): Set[PhiType] = {
    val guardTypes = types(sid, guard, ac)
    val leftTypes = types(sid, left, ac)
    val rightTypes = types(sid, right, ac)

    guardTypes.filter(phiType => q.test(leftTypes, (leftType: PhiType) => PhiType.composition(sid, phiType, leftType) match {
      case Some(compositionType) => rightTypes contains compositionType
      case None => false
    }))
  }

  def types(sid: SID, gslFormula: GslFormula, ac: AliasingConstraint): Set[PhiType] = gslFormula match {
    case atom: Atom => atom match {
      case Atom.Emp() => Set(PhiType.empty)
      case Equality(left, right) => if (ac =:= (left, right)) Set(PhiType.empty) else Set()
      case DisEquality(left, right) => if (ac =:= (left, right)) Set() else Set(PhiType.empty)
      case p: PointsTo => Set(PhiType.ptrmodel(sid, ac, p))
      case PredicateCall(pred, args) => Set() // TODO
    }
    case GslFormula.SeparatingConjunction(left, right) => PhiType.composition(sid, types(sid, left, ac), types(sid, right, ac)).toSet
    case GslFormula.StandardConjunction(left, right) => types(sid, left, ac) intersect types(sid, right, ac)
    case GslFormula.Disjunction(left, right) => types(sid, left, ac) union types(sid, right, ac)
    case GslFormula.Negation(guard, negated) => types(sid, guard, ac) diff types(sid, negated, ac)
    case GslFormula.MagicWand(guard, left, right) => magicWandSeptractionHelper(Forall, sid, ac, guard, left, right)
    case GslFormula.Septraction(guard, left, right) => magicWandSeptractionHelper(Exists, sid, ac, guard, left, right)
  }
}

object FixedPoint {
  var state: mutable.Map[(SID.Predicate[SymbolicHeap], AliasingConstraint), mutable.Set[PhiType]] = collection.mutable.Map.empty.withDefaultValue(mutable.Set.empty)
  var finished: mutable.Set[(SID.Predicate[SymbolicHeap], AliasingConstraint)] = mutable.Set.empty

  @tailrec
  def getTypes(sid: SID, x: Set[Var], predName: String, ac: AliasingConstraint): Iterable[PhiType] = {
    val pred = sid.predicates(predName)
    val tuple = (pred, ac)
    if (finished contains tuple) {
      state(tuple).toSet
    } else {
      val newTypes = mutable.Set.empty[PhiType]
      for (rule <- pred.rules) {
        newTypes.addAll(TypeComputation.ptypes(sid, x, rule, ac))
      }

      if (newTypes.isEmpty) {
        finished.add(tuple)
        state(tuple)
      } else {
        state(tuple).addAll(newTypes)
        getTypes(sid, x, predName, ac)
      }
    }
  }

  def apply(pred: SID.Predicate[SymbolicHeap], ac: AliasingConstraint): Set[PhiType] = state((pred, ac)).toSet
}