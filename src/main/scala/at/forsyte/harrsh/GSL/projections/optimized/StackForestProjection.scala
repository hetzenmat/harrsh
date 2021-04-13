package at.forsyte.harrsh.GSL.projections.optimized

import at.forsyte.harrsh.GSL.GslFormula.Atom.PointsTo
import at.forsyte.harrsh.GSL.projections.optimized.StackForestProjection.{boundVariables, freeVariables}
import at.forsyte.harrsh.GSL.{AliasingConstraint, RuleInstance, SID_btw, Substitution, Utils}
import at.forsyte.harrsh.seplog.{BoundVar, Var}
import TreeProjection.{PredicateCall, TreeProjection, orderingPredicateCall, orderingTreeProjection}

import scala.annotation.tailrec
import scala.collection.{Searching, SortedSet}
import scala.runtime.ScalaRunTime


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
  * Conversion of quantified variables:
  *   - Exists: α_i <=> i * -2 + 1
  *   - Forall: β_i <=> i * -2
  */
class StackForestProjection(val guardedExistentials: Int,
                            val guardedUniversals: Int,
                            val formula: IndexedSeq[TreeProjection]) extends Ordered[StackForestProjection] {

  Utils.debugRequire(guardedExistentials >= 0 && guardedUniversals >= 0)
  Utils.debugRequire(Utils.isSortedStrict(formula)(TreeProjection.orderingTreeProjection))

  val forall: String = "\u03b2" // β
  "\u03b1"
  val quantifiedLength: Int = guardedExistentials + guardedUniversals
  val boundVars: Set[Int] = boundVariables(formula)

  Utils.debugRequireMsg(boundVars.size == quantifiedLength,
                        "Set of bound variables is not equal to set of quantified variables")

  val freeVars: Set[Int] = freeVariables(formula)

  // Finished
  def impliedSet: Set[StackForestProjection] = {
    (for (univ <- SortedSet.from(1 to guardedUniversals).subsets()) yield {

      val subst: Substitution[Int] = Substitution.from(univ.zipWithIndex.map({
        case (variable, index) =>
          (-2 * variable, -2 * (guardedExistentials + index + 1) + 1)
      }))

      StackForestProjection.normalized(guardedExistentials + univ.size,
                                        guardedUniversals - univ.size,
                                        formula.map(TreeProjection.substitute(_, subst)))
    }).toSet
  }

  /**
    * Finished
    */
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
    *
    * Finished
    */
  def isDelimited(sid: SID_btw): Boolean =
    formula.flatten.forall(call => sid.getRootArgument(call) > 0) && {
      val allPredCallsLeft: Seq[PredicateCall] = formula.iterator.flatMap(tp => TreeProjection.getHolePreds(tp)).toSeq
      val setLeftRootArgs = allPredCallsLeft.map(call => sid.getRootArgument(call)).toSet

      setLeftRootArgs.size == allPredCallsLeft.size
    }

  /**
    * Compute the set of all one-step derivable projections wrt. to the generalized modus ponens rule (Definition 7.29)
    *
    * Finished
    */
  def oneStepDerivableSet: Set[StackForestProjection] = {

    val derivableSet = collection.mutable.Set.empty[StackForestProjection]
    var i = 0
    while (i < formula.size) {
      val currentTP: TreeProjection = formula(i)
      val currentRootPred: PredicateCall = TreeProjection.getRootPred(currentTP)

      var j = 0
      while (j < formula.size) {
        if (i != j) {
          val tp: TreeProjection = formula(j)

          tp.search(currentRootPred, 0, tp.size - 2 /* exclude root pred */)(orderingPredicateCall) match {
            case Searching.Found(foundIndex) =>
              val newTP = Utils.insertInstead(tp, foundIndex, TreeProjection.getHolePreds(currentTP))

              var k = -1
              val otherProjections = formula.filter { _ =>
                k += 1
                k != i && k != j
              }

              derivableSet.add(StackForestProjection.normalized(guardedExistentials,
                                                                 guardedUniversals,
                                                                 newTP +: otherProjections))
          }
        }
        j += 1
      }

      i += 1
    }

    derivableSet.toSet
  }

  // Finished
  def substitute(subst: Substitution[Int]): StackForestProjection = {
    val subst2 = subst.filterKeys(_ > 0)

    StackForestProjection.normalized(guardedExistentials, guardedUniversals, formula.map(TreeProjection.substitute(_, subst2)))
  }

  // Finished
  def forget(ac: AliasingConstraint[Int], x: Int): StackForestProjection = {
    if (freeVars.contains(x)) {
      if (ac.isLone(x)) {
        val newGuardedExistentials = guardedExistentials + 1
        val newEx = newGuardedExistentials * -2 + 1
        val subst = Substitution.from(Seq(x -> newEx))

        StackForestProjection.normalized(newGuardedExistentials, guardedUniversals, formula.map(TreeProjection.substitute(_, subst)))
      } else {
        val eqClass = ac.getEquivalenceClass(x)
        val nextLargest = if (eqClass.contains(0)) 0 else eqClass.diff(Set(x)).max

        val subst = Substitution.from(Seq(x -> nextLargest))
        StackForestProjection.normalized(guardedExistentials, guardedUniversals, formula.map(TreeProjection.substitute(_, subst)))
      }
    } else {
      this
    }
  }

  // Finished
  def extend(x: Int): Set[StackForestProjection] = {
    Utils.debugRequire(x > 0)
    Utils.debugRequire(!freeVars.contains(x))

    (1 to guardedUniversals).map(index => {
      val subst = Substitution.from((index * -2 -> x) +: (index + 1 to guardedUniversals).map(i => i * -2 -> (i - 1) * -2))
      StackForestProjection.normalized(guardedExistentials, guardedUniversals - 1, formula.map(TreeProjection.substitute(_, subst)))
    }).toSet
  }

  def repr(sid: SID_btw): String = {
    (if (guardedExistentials > 0) (1 to guardedExistentials).map(BoundVar.apply).mkString("∃ ", " ", ". ") else "") +
      (if (guardedUniversals > 0) (guardedExistentials + 1 to guardedExistentials + 1 + guardedUniversals).map(BoundVar.apply).mkString("∀ ", " ", ". ") else "") +
      formula.map(TreeProjection.reprTreeProjection(_, sid)).mkString(" * ")
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case v: StackForestProjection =>
        v.guardedExistentials == guardedExistentials && v.guardedUniversals == guardedUniversals && v.formula == formula

      case _ => false
    }
  }

  override def hashCode(): Int = {
    ScalaRunTime._hashCode((guardedExistentials, guardedUniversals, formula))
  }

  override def compare(that: StackForestProjection): Int = {
    StackForestProjection.ord.compare((guardedExistentials, guardedUniversals, formula), (that.guardedExistentials, that.guardedUniversals, that.formula))
  }

}

object StackForestProjection {

  val ord: Ordering[(Int, Int, IndexedSeq[TreeProjection])] = Ordering.Tuple3[Int, Int, IndexedSeq[TreeProjection]](Ordering[Int], Ordering[Int], Ordering.Implicits.seqOrdering[IndexedSeq, TreeProjection](TreeProjection.orderingTreeProjection))

  val sortedSetOrd: Ordering[SortedSet[TreeProjection]] = Ordering.Implicits.sortedSetOrdering[SortedSet, TreeProjection](TreeProjection.orderingTreeProjection)

  val empty: StackForestProjection = new StackForestProjection(0, 0, IndexedSeq.empty)

  def normalized(exCount: Int, uvCount: Int, tps: IndexedSeq[TreeProjection]): StackForestProjection = {
    var exCounter = exCount
    var uvCounter = uvCount

    val formulaSorted = tps.sorted(orderingTreeProjection)
    val variableIterator = Utils.chainIterators(formulaSorted, tp => TreeProjection.variableIterator(tp))
    val quantSubst = Substitution.empty[Int]
    while (variableIterator.hasNext) {
      val variable = variableIterator.next()
      if (variable < 0 && !quantSubst.isDefinedAt(variable)) {
        if (variable % 2 != 0) {
          // exists
          quantSubst.add(variable, exCounter * -2 + 1)
          exCounter -= 1
        } else {
          // forall
          quantSubst.add(variable, uvCounter * -2)
          uvCounter -= 1
        }
      }
    }

    Utils.debugRequire(exCounter == 0 && uvCounter == 0)

    new StackForestProjection(exCount,
                              uvCount,
                              formulaSorted.map(tp => TreeProjection.substitute(tp, quantSubst)))
  }

  // Finished
  def fromPtrmodel(ac: AliasingConstraint[Int], inst: RuleInstance, model: Map[Int, Int], pointsTo: PointsTo, sid: SID_btw): StackForestProjection = {
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

    val variableIterator = TreeProjection.variableIterator(tpWithoutQuantifiedVars)
    var univCount = universalQuantified.size
    val substitution = Substitution.empty[Int]
    while (variableIterator.hasNext) {
      val variable = variableIterator.next()
      if (variable < 0 && !substitution.isDefinedAt(variable)) {
        substitution.add(variable, univCount * -2)
        univCount -= 1
      }
    }

    Utils.debugRequire(univCount == 0)

    new StackForestProjection(0, universalQuantified.size, IndexedSeq(TreeProjection.substitute(tpWithoutQuantifiedVars, substitution)))
  }

  private def formulaFlatMap[A](formula: Iterable[TreeProjection], f: PredicateCall => Iterable[A]): Iterable[A] =
    formula.flatMap(tp => tp.flatMap(predCall => f(predCall)))

  def boundVariables(formula: Iterable[TreeProjection]): Set[Int] = formulaFlatMap(formula, predCall => predCall.tail.filter(_ < 0)).toSet

  def freeVariables(formula: Iterable[TreeProjection]): Set[Int] = formulaFlatMap(formula, predCall => predCall.tail.filter(_ >= 0)).toSet

  def composition(left: StackForestProjection, right: StackForestProjection, sid: SID_btw): Set[StackForestProjection] = {
    Utils.debugRequire(allRescopings(left, right) == allRescopings(right, left))

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

  def unapply(treeProjection: TreeProjection): Option[(IndexedSeq[PredicateCall], PredicateCall)] = {
    if (treeProjection.isEmpty) None
    else
      Some(getHolePreds(treeProjection), getRootPred(treeProjection))
  }

  val orderingPredicateCall: Ordering[PredicateCall] = Ordering.Implicits.seqOrdering[IndexedSeq, Int]
  val orderingTreeProjection: Ordering[TreeProjection] = Ordering.Implicits.seqOrdering[IndexedSeq, PredicateCall](orderingPredicateCall)

  def variableIterator(treeProjection: TreeProjection): Iterator[Int] = new Iterator[Int] {
    var currentPred = 0
    var currentVar = 0

    override def hasNext: Boolean = currentPred <= treeProjection.size && currentVar <= arity(treeProjection(currentPred))

    override def next(): Int = {
      val pred = treeProjection(currentPred)
      val variable = pred(currentVar)

      currentVar = (currentVar + 1) % arity(pred)
      if (currentVar == 0) currentPred += 1

      variable
    }
  }

  @inline def arity(predicateCall: PredicateCall): Int = predicateCall.size - 1

  @inline def reprPredicateCall(predicateCall: PredicateCall, sid: SID_btw): String = {
    sid.predBiMap.reverse(predicateCall.head) + predicateCall.tail.map(sid.varBiMap.reverse).mkString("(", ", ", ")")
  }

  @inline def reprTreeProjection(treeProjection: TreeProjection, sid: SID_btw): String =
    if (treeProjection.size == 1) // only rootpred
      TreeProjection.reprPredicateCall(treeProjection.head, sid)
    else
      "(" + TreeProjection.getHolePreds(treeProjection).map(pred => TreeProjection.reprPredicateCall(pred, sid)).mkString(" * ") + " -* " + TreeProjection.reprPredicateCall(TreeProjection.getRootPred(treeProjection), sid) + ")"

  @inline def variableSequence(tp: TreeProjection): IndexedSeq[Int] = tp.flatMap(_.tail)

  @inline def create(rootpred: PredicateCall, allholepreds: IndexedSeq[PredicateCall]): TreeProjection = {
    Utils.debugRequire(Utils.isSorted(allholepreds)(TreeProjection.orderingPredicateCall))
    allholepreds :+ rootpred
  }

  @inline def getRootPred(tp: TreeProjection): PredicateCall = tp.last

  @inline def getHolePreds(tp: TreeProjection): IndexedSeq[PredicateCall] = tp.init

  @inline def substitute(tp: TreeProjection, subst: Substitution[Int]): TreeProjection = tp.map(p => substitutePred(p, subst))

  @inline private def substitutePred(pred: PredicateCall, subst: Substitution[Int]): IndexedSeq[Int] =
    pred.head +: pred.tail.map(subst.apply)
}