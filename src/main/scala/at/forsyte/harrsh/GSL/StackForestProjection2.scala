package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Multiplicity, NullConst, Var}

import scala.+:
import scala.annotation.tailrec
import scala.collection.SortedSet
import scala.runtime.ScalaRunTime
import TreeProjection.{PredicateCall, TreeProjection, orderingTreeProjection}
import at.forsyte.harrsh.GSL.GslFormula.Atom.PointsTo
import at.forsyte.harrsh.GSL.StackForestProjection2.{boundVariables, freeVariables}

/**
  * Created by Matthias Hetzenberger on 2021-02-12
  *
  * An efficient representation for stack-forest projections is important because they are the most used object during type computation.
  * Hence, desirable fast operations are:
  *   - Equality test (since stack-forest projections are identified up to the presented rewriting equality naive equality testing
  *     would lead to a runtime behaviour of O(n!) where n represents the number of quantified variables, because in the worst case
  *     all possible permutations of renamings need to be enumerated)
  *   - Comparison (for usage with sorted sets)
  *   - Substitutions, Extensions, Forgetting, Rescopings
  *
  * To achieve fast equality testing I use a technique similar to De Bruijn indices which are used in lambda calculus to
  * obtain "free" α-equivalence between terms.
  *
  * The first idea is to represent each occurrence of a bound variable by its multiplicity, i.e., how often it occurs in the projection.
  * But this is not sound since then ∃ e1 e2. (P(e1) * P(e2) -* P(a)) * (P(e2) * P(e1) -* P(b)) and ∃ e1 e2. (P(e1) * P(e1) -* P(a)) * (P(e2) * P(e2) -* P(b)) would
  * be considered equal.
  *
  * Instead, the existential and universal variables are encoding with negative numbers s.t. odd numbers are existential and odd numbers are universal.
  * Moreover, the encodings of the quantified variables are ordered with respect to the occurrence with the smallest position.
  *
  * A stack-forest projection
  */
class StackForestProjection2(val guardedExistentials: Int,
                             val guardedUniversals: Int,
                             val formula: SortedSet[TreeProjection]) extends Ordered[StackForestProjection2] {

  Utils.debugRequire(guardedExistentials >= 0 && guardedUniversals >= 0)

  val quantifiedLength: Int = guardedExistentials + guardedUniversals
  val boundVars: Set[Int] = boundVariables(formula)

  Utils.debugRequireMsg(boundVars.size == quantifiedLength,
                        "Set of bound variables is not equal to set of quantified variables")

  val freeVars: Set[Int] = freeVariables(formula)

  def impliedSet(sid: SID_btw): Set[StackForestProjection] = {
    (for (univ <- guardedUniversals.unsorted) yield {
      val newBound = BoundVar(guardedExistentials.size + 1)
      val newUniv = BoundVar.from(1, guardedUniversals.size - 1, guardedExistentials.size + 1)

      val subst: Map[Var, Var] = ((univ, newBound) +: guardedUniversals.diff(Set(univ)).toSeq.zip(newUniv)).toMap

      val sf = new StackForestProjection(guardedExistentials.union(Set(newBound)), SortedSet.from(newUniv), formula.map(_.substitute(subst)))

      sf.impliedSet(sid).incl(sf)
    }).flatten.toSet.incl(this): Set[StackForestProjection]
  }

  def replaceQuantifiedVariables(replacements: Seq[Int]): Iterable[TreeProjection] = {
    Utils.debugRequireMsg(guardedExistentials + guardedUniversals == replacements.size,
                          "Size of quantified variables does not match")

    val replEx = replacements.take(guardedExistentials)
    val replUn = replacements.drop(guardedExistentials)

    val subst: Map[Int, Int] = (guardedExistentials.zip(replEx) ++ guardedUniversals.zip(replUn)).toMap
    formula.map({ case TreeProjection(calls, call) => TreeProjection(calls.map(_.substitute(subst)), call.substitute(subst)) })
  }

  def deriveGreedy: Set[StackForestProjection] = {
    val s = oneStepDerivableSet

    if (s.isEmpty) Set(this)
    else
      s.flatMap(_.deriveGreedy)
  }

  def derivableSet: Set[StackForestProjection] = {

    @tailrec
    def aux(prev: Set[StackForestProjection]): Set[StackForestProjection] = {
      val next = prev.union(prev.flatMap(_.oneStepDerivableSet))
      if (next == prev)
        next
      else aux(next)
    }

    val r = aux(Set(this))

    r
  }


  /**
    * Determine if the projection is delimited wrt. to the given SID (Definition 8.2).
    */
  def isDelimited(sid: SID_btw): Boolean =
    formula.flatten.forall(call => sid.getRootArgument(call) > 0) && {
      val allPredCallsLeft: Seq[PredicateCall] = formula.iterator.flatMap(tp => TreeProjection.getHolePreds(tp)).toSeq
      val setLeftRootArgs = allPredCallsLeft.map(call => sid.getRootArgument(call)).toSet

      setLeftRootArgs.size == allPredCallsLeft.size
    }

  /**
    * Compute the set of all one-step derivable projections wrt. to the generalized modus ponens rule (Definition 7.29)
    */
  def oneStepDerivableSet: Set[StackForestProjection] = {
    val formulaWithIndex = formula.zipWithIndex
    (for (projs <- formulaWithIndex;
          i = projs._2;
          f = projs._1) yield {
      formulaWithIndex.flatMap({
        case (TreeProjection(calls, rootpred), j) if i != j =>
          val ix = calls.indexOf(f.rootpred)

          if (ix == -1)
            None
          else {
            val newProj = TreeProjection((calls.zipWithIndex.collect({ case (v, k) if k != ix => v }) ++ f.allholepreds).sorted,
                                         rootpred)

            val newFormulas = formulaWithIndex.collect({ case (v, k) if k != i && k != j => v }) union (Set(newProj))
            val boundVars = boundVariables(newFormulas)
            Some(new StackForestProjection(guardedExistentials.intersect(boundVars),
                                           guardedUniversals.intersect(boundVars),
                                           SortedSet.from(newFormulas)))
          }
        case _ => None
      }).toSet
    }).flatten.toSet
  }

  def substitute(subst: Map[Var, Var]): StackForestProjection = {
    val subst2 = subst.filter({
      case (_: BoundVar, _) => false
      case _ => true
    })

    new StackForestProjection(guardedExistentials, guardedUniversals, formula.map(_.substitute(subst2)))
  }

  def forget(ac: AliasingConstraint[Var], x: FreeVar): StackForestProjection = {

    if (freeVars.contains(x)) {
      if (ac.isLone(x)) {
        val bound = BoundVar(guardedExistentials.size + 1)
        val newUniversals = guardedUniversals.map(u => BoundVar(u.index + 1))

        val subst = guardedUniversals.zip(newUniversals).toMap.asInstanceOf[Map[Var, Var]].updated(x, bound)

        new StackForestProjection(guardedExistentials.union(Set(bound)), newUniversals, formula.map(_.substitute(subst)))
      } else {
        val eqClass = ac.getEquivalenceClass(x)
        val nextLargest = if (eqClass.contains(NullConst)) NullConst else eqClass.diff(Set(x)).max

        require(nextLargest != NullConst)

        val subst: Map[Var, Var] = Map((x, nextLargest))
        new StackForestProjection(guardedExistentials, guardedUniversals, formula.map(_.substitute(subst)))
      }
    } else {
      this
    }
  }

  def extend(x: FreeVar): Set[StackForestProjection] = {
    require(!freeVars.contains(x))

    guardedUniversals.unsorted.map(bv => {
      val newUniversals = guardedUniversals.diff(Set(bv))
      val bvarSubst: Map[BoundVar, BoundVar] = (bv.index + 1 to quantifiedLength).zip(LazyList.from(bv.index))
                                                                                 .map(t => (BoundVar(t._1), BoundVar(t._2)))
                                                                                 .toMap

      new StackForestProjection(guardedExistentials, SortedSet.from(newUniversals.unsorted.map(i => bvarSubst.getOrElse(i, i))), formula.map(_.substitute(bvarSubst.asInstanceOf[Map[Var, Var]].updated(bv, x))))
    }).toSet
  }

  def repr(sid: SID_btw): String = {
    (if (guardedExistentials > 0) (1 to guardedExistentials).map(BoundVar.apply).mkString("∃ ", " ", ". ") else "") +
      (if (guardedUniversals > 0) (guardedExistentials + 1 to guardedExistentials + 1 + guardedUniversals).map(BoundVar.apply).mkString("∀ ", " ", ". ") else "") + formula.map(tp =>
      if (tp.size == 1) // only rootpred
        call.toString
      else
        "(" + calls.head + " -* " + call + ")"
      else
        "((" + calls.mkString(" * ") + ") -* " + call + ")"
    ).mkString(" * ")
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case v: StackForestProjection2 =>
        v.guardedExistentials == guardedExistentials && v.guardedUniversals == guardedUniversals && v.formula == formula

      case _ => false
    }
  }

  override def hashCode(): Int = {
    ScalaRunTime._hashCode((guardedExistentials, guardedUniversals, formula))
  }

  override def compare(that: StackForestProjection2): Int = {
    StackForestProjection2.ord.compare((guardedExistentials, guardedUniversals, formula), (that.guardedExistentials, that.guardedUniversals, that.formula))
  }

}

object StackForestProjection2 {

  val ord: Ordering[(Int, Int, SortedSet[TreeProjection])] = Ordering.Tuple3[Int, Int, SortedSet[TreeProjection]](Ordering[Int], Ordering[Int], Ordering.Implicits.sortedSetOrdering[SortedSet, TreeProjection](TreeProjection.orderingTreeProjection))

  val sortedSetOrd: Ordering[SortedSet[TreeProjection]] = Ordering.Implicits.sortedSetOrdering[SortedSet, TreeProjection](TreeProjection.orderingTreeProjection)

  val empty: StackForestProjection2 = new StackForestProjection2(0, 0, SortedSet.empty(sortedSetOrd))

  // Finished
  def fromPtrmodel(ac: AliasingConstraint[Int], inst: RuleInstance, model: Map[Int, Int], pointsTo: PointsTo, sid: SID_btw): StackForestProjection2 = {
    val imgS: Set[Int] = model.values.toSet

    // Set[Int] : forall i, i > 0
    val universalQuantified: Set[Int] = inst.locs.diff(imgS)

    // model: var -> loc
    val stackRepl = (model.toSeq.map(_.swap).filter(_._1 > 0).map(kv => (kv._1, AliasingConstraint.largestAliasInt(ac, kv._2)))
      ++ universalQuantified.map(loc => (loc, -loc))).toMap
    // stackRepl: loc -> var

    val createPredCall: ((String, Seq[Int])) => PredicateCall = {
      case (predName, args) =>
        (sid.predBiMap.forward(predName) +: args.map(stackRepl.apply)).toIndexedSeq
    }

    val rootPred: PredicateCall = createPredCall(inst.pred.name, inst.predArgs)
    val holePreds: IndexedSeq[PredicateCall] = inst.calls.map(createPredCall).toIndexedSeq

    val tpWithoutQuantifiedVars = TreeProjection.create(rootPred, holePreds.sorted(TreeProjection.orderingPredicateCall))

    val quantifiedSubst: Map[Int, Int] = TreeProjection.variableSequence(tpWithoutQuantifiedVars).foldLeft((1, Map.empty[Int, Int]))({
      case ((count, map), variable) =>
        if (variable < 0 && !map.contains(variable)) {
          (count + 1, map.updated(variable, count * -2))
        } else (count, map)
    })._2

    new StackForestProjection2(0, universalQuantified.size, SortedSet(TreeProjection.substitute(tpWithoutQuantifiedVars, quantifiedSubst))(orderingTreeProjection))
  }

  private def formulaFlatMap[A](formula: Iterable[TreeProjection], f: PredicateCall => Iterable[A]): Iterable[A] =
    formula.flatMap(tp => tp.flatMap(predCall => f(predCall)))

  def boundVariables(formula: Iterable[TreeProjection]): Set[Int] = formulaFlatMap(formula, predCall => predCall.tail.filter(_ < 0)).toSet

  def freeVariables(formula: Iterable[TreeProjection]): Set[Int] = formulaFlatMap(formula, predCall => predCall.tail.filter(_ >= 0)).toSet

  def composition(left: StackForestProjection, right: StackForestProjection, sid: SID_btw): Set[StackForestProjection] = {
    //    val r = if (left.compare(right) <= 0)
    //      allRescopings(left, right).filter(_.isDelimited(sid)).flatMap(sfp => sfp.deriveGreedy /*.incl(sfp) TODO*/)
    //    else
    //      allRescopings(right, left).filter(_.isDelimited(sid)).flatMap(sfp => sfp.deriveGreedy /*.incl(sfp) TODO*/)
    //    val r = allRescopings(left, right).flatMap(sfp => sfp.derivableSet /*.incl(sfp) TODO*/)

    //(allRescopings(left, right) union allRescopings(right, left)).flatMap(sfp => sfp.derivableSet /*.incl(sfp) TODO*/)

    allRescopings(left, right).flatMap(sfp => sfp.derivableSet)
  }

  def allRescopings(left: StackForestProjection, right: StackForestProjection): Set[StackForestProjection] = {
    val existentials = SortedSet.from(BoundVar.from(1, left.guardedExistentials.size + right.guardedExistentials.size))

    val universal: Left[Unit, BoundVar] = Left(())

    def getCombinations(current: StackForestProjection, other: StackForestProjection, offset: Int): Seq[Seq[(BoundVar, Either[Unit, BoundVar])]] = {
      def loop(s: Int): Seq[Seq[(BoundVar, Either[Unit, BoundVar])]] = {
        if (s > current.guardedUniversals.size)
          Seq(Seq.empty)
        else {
          val others = loop(s + 1)

          val choices: Seq[(BoundVar, Either[Unit, BoundVar])] = LazyList
            .continually(BoundVar(s))
            .zip(LazyList.from(offset)
                         .take(other.guardedExistentials.size)
                         .map(i => Right(BoundVar(i))))

          others.flatMap(seq => {
            ((BoundVar(s), universal) +: seq) +: choices.map(head => head +: seq)
          })
        }
      }

      loop(1)
    }


    val leftCombinations = getCombinations(left, right, left.guardedExistentials.size + 1)
    val rightCombinations = getCombinations(right, left, 1)

    def aux(max: Int, vars: Seq[Either[BoundVar, BoundVar]]): Seq[Seq[(Either[BoundVar, BoundVar], BoundVar)]] = {
      vars match {
        case Seq() => Seq(Seq())
        case head +: tail =>

          (for (i <- 1 to max) yield {
            aux(max, tail).map(s => (head, BoundVar(i)) +: s)
          }).flatten

      }
    }

    (for (leftCombination <- leftCombinations;
          rightCombination <- rightCombinations;
          leftUnivs = leftCombination.collect { case (boundVar, Left(_)) => boundVar };
          rightUnivs = rightCombination.collect { case (boundVar, Left(_)) => boundVar }) yield {

      val combs = aux(leftUnivs.size + rightUnivs.size,
                      left.guardedUniversals.toSeq.map(Left.apply) ++ right.guardedUniversals.toSeq.map(Right.apply))
        .filter(seq => {
          val idxs = seq.map(_._2.index).toSet
          idxs == Set.from(1 to idxs.size)
        })

      val leftExistentials = leftCombination.collect { case (boundVar, Right(repl)) => (boundVar, repl) }
      val rightExistentials = rightCombination.collect { case (boundVar, Right(repl)) => (boundVar, repl) }

      if (combs.isEmpty) {

        val leftRemapping: Map[Var, Var] = leftExistentials.toMap
        val rightRemapping: Map[Var, Var] = (rightExistentials ++
          (1 to right.guardedExistentials.size).map(i => (BoundVar(i), BoundVar(i + left.guardedExistentials.size)))
          ).toMap

        Seq(new StackForestProjection(existentials,
                                      SortedSet.from(BoundVar.from(1, leftUnivs.size + rightUnivs.size, existentials.size)),
                                      left.formula.map(_.substitute(leftRemapping)) ++ right.formula.map(_.substitute(rightRemapping))))
      } else
        combs.map(seq => {
          val seqOffset = seq.map({ case (value, boundVar) => (value, BoundVar(boundVar.index + existentials.size)) })
          val universalSet = SortedSet.from(seqOffset.map(_._2))
          val leftUnivMapping: Seq[(BoundVar, BoundVar)] = seqOffset.collect { case (Left(v), boundVar) => (v, boundVar) }
          val rightUnivMapping: Seq[(BoundVar, BoundVar)] = seqOffset.collect { case (Right(v), boundVar) => (v, boundVar) }

          val leftRemapping: Map[Var, Var] = (leftExistentials ++ leftUnivMapping).toMap
          val rightRemapping: Map[Var, Var] = (rightExistentials ++
            rightUnivMapping ++
            (1 to right.guardedExistentials.size).map(i => (BoundVar(i), BoundVar(i + left.guardedExistentials.size)))).toMap

          new StackForestProjection(existentials,
                                    universalSet,
                                    left.formula.map(_.substitute(leftRemapping)) ++ right.formula.map(_.substitute(rightRemapping)))
        })

    }).flatten.toSet
  }
}

/**
  * A predicate call is represented by an indexed sequence of integers, where the first int corresponds to the predicate
  * and the following integers represent the variables which are the arguments of the predicate.
  *
  * A tree projection is then represented by an indexed sequence of predicate calls, where the first predicate call
  * corresponds to the root predicate and the following predicate calls represent the hole predicates.
  */
object TreeProjection {
  type PredicateCall = IndexedSeq[Int]
  type TreeProjection = IndexedSeq[PredicateCall]

  val orderingPredicateCall: Ordering[PredicateCall] = Ordering.Implicits.seqOrdering[IndexedSeq, Int]
  val orderingTreeProjection: Ordering[TreeProjection] = Ordering.Implicits.seqOrdering[IndexedSeq, PredicateCall](orderingPredicateCall)

  @inline def reprPredicateCall(predicateCall: PredicateCall, sid: SID_btw): String = {
    sid.predBiMap.reverse(predicateCall.head) + predicateCall.tail.map(sid.varBiMap.reverse).mkString("(", ", ", ")")
  }

  @inline def variableSequence(tp: TreeProjection): IndexedSeq[Int] = tp.flatMap(_.tail)

  @inline def create(rootpred: PredicateCall, allholepreds: IndexedSeq[PredicateCall]): TreeProjection = {
    Utils.debugRequire(Utils.isSorted(allholepreds)(TreeProjection.orderingPredicateCall))
    allholepreds :+ rootpred
  }

  @inline def getRootPred(tp: TreeProjection): PredicateCall = tp.last

  @inline def getHolePreds(tp: TreeProjection): IndexedSeq[PredicateCall] = tp.init

  @inline def substitute(tp: TreeProjection, subst: Map[Int, Int]): TreeProjection = tp.map(p => substitutePred(p, subst))

  @inline private def substitutePred(pred: PredicateCall, subst: Map[Int, Int]): IndexedSeq[Int] =
    pred.head +: pred.tail.map(i => subst.getOrElse(i, i))
}