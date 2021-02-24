package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{DisEquality, Equality, PointsTo, PredicateCall}
import at.forsyte.harrsh.seplog.{FreeVar, Var}

import scala.annotation.tailrec
import scala.collection.mutable

class TypeComputation(val sid: SID_btw, val x: Set[Var]) {

  private val state: mutable.Map[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint), mutable.Set[PhiType]] = collection.mutable.Map.empty.withDefaultValue(mutable.Set.empty)
  private val finished: mutable.Set[(SID.Predicate[SymbolicHeapBtw], AliasingConstraint)] = mutable.Set.empty

  def ptypes(atom: Atom, ac: AliasingConstraint): Iterable[PhiType] = atom match {
    case e: Equality => types(e, ac)
    case d: DisEquality => types(d, ac)
    case p: PointsTo => types(p, ac)
    case PredicateCall(predName, args) =>
      val pred = sid.predicates(predName)

      val parameters = pred.args.map(FreeVar)

      val acExtended = ac.reverseRenaming(parameters, args)
      val acExtendedRestricted = acExtended.restricted(x.union(parameters.toSet))

      val types = state((pred, acExtendedRestricted))
      val typesRenamed = PhiType.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac, types)

      val typesExtended = PhiType.extend(ac, acExtended, typesRenamed)

      typesExtended
  }

  def ptypes(atoms: Seq[Atom], ac: AliasingConstraint): Iterable[PhiType] = atoms match {
    case atom +: Seq() => ptypes(atom, ac)
    case head +: rest => PhiType.composition(sid, ptypes(head, ac), ptypes(rest, ac))
  }

  def ptypes(sh: SymbolicHeapBtw, ac: AliasingConstraint): Iterable[PhiType] =
    if (sh.quantifiedVars.nonEmpty) {
      val fresh = Var.freshFreeVar(x.union(sh.freeVars))
      val allExtensions = ac.allExtensions(fresh)
      allExtensions.flatMap(ac_ => {
        val types = ptypes(sh.dropFirstQuantifiedVar(fresh), ac_)
        PhiType.forget(sid, ac_, fresh, types)
      })
    } else ptypes(sh.atoms, ac)

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
                                         ac: AliasingConstraint,
                                         guard: GslFormula,
                                         left: GslFormula,
                                         right: GslFormula): Set[PhiType] = {
    val guardTypes = types(guard, ac)
    val leftTypes = types(left, ac)
    val rightTypes = types(right, ac)

    guardTypes.filter(phiType => q.test(leftTypes, (leftType: PhiType) => PhiType.composition(sid, phiType, leftType) match {
      case Some(compositionType) => rightTypes contains compositionType
      case None => false
    }))
  }

  def types(gslFormula: GslFormula, ac: AliasingConstraint): Set[PhiType] = gslFormula match {
    case atom: Atom => atom match {
      case Atom.Emp() => Set(PhiType.empty)
      case Equality(left, right) => if (ac =:= (left, right)) Set(PhiType.empty) else Set()
      case DisEquality(left, right) => if (ac =:= (left, right)) Set() else Set(PhiType.empty)
      case p: PointsTo => Set(PhiType.ptrmodel(sid, ac, p))
      case PredicateCall(predName, args) =>
        val pred = sid.predicates(predName)

        val parameters = pred.args.map(FreeVar)
        val acParams = ac.reverseRenaming(parameters, args)

        val types = unfold(pred, acParams).toSet

        types.map(_.rename(parameters, args.asInstanceOf[Seq[FreeVar]], ac))
    }
    case GslFormula.SeparatingConjunction(left, right) => PhiType.composition(sid, types(left, ac), types(right, ac)).toSet
    case GslFormula.StandardConjunction(left, right) => types(left, ac) intersect types(right, ac)
    case GslFormula.Disjunction(left, right) => types(left, ac) union types(right, ac)
    case GslFormula.Negation(guard, negated) => types(guard, ac) diff types(negated, ac)
    case GslFormula.MagicWand(guard, left, right) => magicWandSeptractionHelper(Forall, ac, guard, left, right)
    case GslFormula.Septraction(guard, left, right) => magicWandSeptractionHelper(Exists, ac, guard, left, right)
  }

  @tailrec
  private def unfold(pred: SID.Predicate[SymbolicHeapBtw], ac: AliasingConstraint): mutable.Set[PhiType] = {
    val tuple = (pred, ac)
    if (finished contains tuple) {
      state(tuple)
    } else {
      val newTypes = mutable.Set.empty[PhiType]
      for (rule <- pred.rules) {
        newTypes.addAll(ptypes(rule, ac))
      }

      if (newTypes.isEmpty) {
        finished.add(tuple)
        state(tuple)
      } else {
        state(tuple).addAll(newTypes)
        unfold(pred, ac)
      }
    }
  }
}