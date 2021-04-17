package at.forsyte.harrsh.GSL.projections

import at.forsyte.harrsh.GSL.GslFormula.Atom
import at.forsyte.harrsh.GSL.GslFormula.Atom.{PointsTo, PredicateCall}
import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.GSL._
import at.forsyte.harrsh.GSL.projections.StackForestProjection.{boundVariables, freeVariables, varSeq}
import at.forsyte.harrsh.GSL.query.QueryContext
import at.forsyte.harrsh.seplog._

import scala.annotation.tailrec
import scala.collection.SortedSet
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
  * A stack-forest projection
  */
class StackForestProjection(val guardedExistentials: SortedSet[BoundVar],
                            val guardedUniversals: SortedSet[BoundVar],
                            val formula: SortedSet[TreeProjection]) extends Ordered[StackForestProjection] {

  Utils.debugRequireMsg(guardedExistentials.intersect(guardedUniversals).isEmpty, "No duplicates between quantifier blocks allowed")
  Utils.debugRequireMsg(guardedExistentials == SortedSet.from(LazyList.from(1).map(BoundVar.apply).take(guardedExistentials.size)),
                        "Quantified variables must have consecutive indices starting with 1")
  Utils.debugRequireMsg(guardedUniversals == SortedSet.from(LazyList.from(guardedExistentials.size + 1).map(BoundVar.apply).take(guardedUniversals.size)),
                        "Quantified variables must have consecutive indices starting with 1")

  val quantifiedLength: Int = guardedExistentials.size + guardedUniversals.size
  val boundVars: Set[BoundVar] = boundVariables(formula)
  val freeVars: Set[FreeVar] = freeVariables(formula)
  val allCalls: SortedSet[Atom.PredicateCall] = formula.flatMap(p => p.allholepreds :+ p.rootpred)
  val variableSeq: Seq[Var] = varSeq(formula)
  val multSubst: Substitution[Var] = Substitution.from(guardedExistentials.toSeq.map(ex => (ex, Multiplicity(variableSeq.count(_ == ex)))) ++
                                                         guardedUniversals.toSeq.map(uv => (uv, Multiplicity(-variableSeq.count(_ == uv)))))
  val formulaMultiplicites: SortedSet[TreeProjection] = formula.map(tp => tp.substitute(multSubst))

  lazy val impliedSet: Set[StackForestProjection] = {
    (for (univ <- guardedUniversals.unsorted) yield {
      val newBound = BoundVar(guardedExistentials.size + 1)
      val newUniv = BoundVar.from(1, guardedUniversals.size - 1, guardedExistentials.size + 1)

      val subst: Substitution[Var] = Substitution.from((univ, newBound) +: guardedUniversals.diff(Set(univ)).toSeq.zip(newUniv))

      val sf = new StackForestProjection(guardedExistentials.union(Set(newBound)), SortedSet.from(newUniv), formula.map(_.substitute(subst)))

      sf.impliedSet.incl(sf)
    }).flatten.toSet.incl(this): Set[StackForestProjection]
  }

  Utils.debugRequireMsg(boundVars == guardedExistentials.union(guardedUniversals),
                        "Set of bound variables is not equal to set of quantified variables")

  def replaceQuantifiedVariables(replacements: Seq[BoundVar]): Iterable[TreeProjection] = {
    Utils.debugRequireMsg(guardedExistentials.size + guardedUniversals.size == replacements.size,
                          "Size of quantified variables does not match")

    val replEx = replacements.take(guardedExistentials.size)
    val replUn = replacements.drop(guardedExistentials.size)

    val subst: Substitution[Var] = Substitution.from(guardedExistentials.zip(replEx) ++ guardedUniversals.zip(replUn))
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
  lazy val isDelimited: Boolean =
    allCalls.forall(call => freeVars.asInstanceOf[Set[Var]].contains(call.args(QueryContext.sid.predicates(call.pred).predrootIndex))) && {

      if (formula.exists(tp => tp.allholepreds.size == 1 && tp.allholepreds.head == tp.rootpred)) {
        //return false
      }

      val cond2 = formula.forall(tp => !tp.allholepreds.contains(tp.rootpred))
      if (!cond2) {
        //return false
      }

      def prop(sf: StackForestProjection): Boolean = {
        val vars = sf.formula.unsorted.map(_.rootpred).map({ case PredicateCall(pred, args) =>
          val p = QueryContext.sid.predicates(pred)
          args(p.predrootIndex)
        }).toSet

        vars.size < sf.formula.size
      }

      if (prop(this)) {
        ???
        //return false
      }

      val allPredCallsLeft: Seq[PredicateCall] = formula.toSeq.flatMap(_.allholepreds)
      val allVars = freeVars.asInstanceOf[Set[Var]].union(boundVars.asInstanceOf[Set[Var]])

      val r = allVars.forall(variable => allPredCallsLeft.count(p => p.args(QueryContext.sid.predicates(p.pred).predrootIndex) == variable) <= 1)

      r
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
            val newProj = projections.TreeProjection((calls.zipWithIndex.collect({ case (v, k) if k != ix => v }) ++ f.allholepreds).sorted,
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

  def substitute(subst: Substitution[Var]): StackForestProjection = {
    val subst2 = subst.filterKeys(!_.isInstanceOf[BoundVar])

    new StackForestProjection(guardedExistentials, guardedUniversals, formula.map(_.substitute(subst2)))
  }

  def forget(ac: AliasingConstraint[Var], x: FreeVar): StackForestProjection = {

    if (freeVars.contains(x)) {
      if (ac.isLone(x)) {
        val bound = BoundVar(guardedExistentials.size + 1)
        val newUniversals = guardedUniversals.map(u => BoundVar(u.index + 1))

        val subst: Substitution[Var] = Substitution.from(guardedUniversals.zip(newUniversals))
        subst.add(x, bound)

        new StackForestProjection(guardedExistentials.union(Set(bound)), newUniversals, formula.map(_.substitute(subst)))
      } else {
        val eqClass = ac.getEquivalenceClass(x)
        val nextLargest = if (eqClass.contains(NullConst)) NullConst else eqClass.diff(Set(x)).max

        require(nextLargest != NullConst)

        val subst: Substitution[Var] = Substitution.singleton((x, nextLargest))
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
      val bvarSubst: Substitution[BoundVar] = Substitution.from((bv.index + 1 to quantifiedLength).zip(LazyList.from(bv.index))
                                                                                                  .map(t => (BoundVar(t._1), BoundVar(t._2))))

      val univ = SortedSet.from(newUniversals.unsorted.map(bvarSubst.apply))
      val subst = bvarSubst.asInstanceOf[Substitution[Var]]
      subst.add(bv, x)
      new StackForestProjection(guardedExistentials,
                                univ,
                                formula.map(_.substitute(subst)))
    }).toSet
  }

  override def toString: String = {
    (if (guardedExistentials.nonEmpty) guardedExistentials.mkString("∃ ", " ", ". ") else "") +
      (if (guardedUniversals.nonEmpty) guardedUniversals.mkString("∀ ", " ", ". ") else "") + formula.map({ case TreeProjection(calls, call) =>
      if (calls.isEmpty)
        call.toString
      else if (calls.size == 1)
        "(" + calls.head + " -* " + call + ")"
      else
        "((" + calls.mkString(" * ") + ") -* " + call + ")"
    }).mkString(" * ")
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case v: StackForestProjection =>
        val r = v.guardedExistentials == guardedExistentials && v.guardedUniversals == guardedUniversals && formulaMultiplicites == v.formulaMultiplicites

        if (r && toString != v.toString) {
          print("")
        }

        r
      case _ => false
    }
  }

  override def hashCode(): Int = {
    ScalaRunTime._hashCode((guardedExistentials, guardedUniversals, formulaMultiplicites))
  }

  override def compare(that: StackForestProjection): Int = {
    if (guardedExistentials.size < that.guardedExistentials.size) -1
    else if (guardedExistentials.size > that.guardedExistentials.size) 1
    else {
      if (guardedUniversals.size < that.guardedUniversals.size) -1
      else if (guardedUniversals.size > that.guardedUniversals.size) 1
      else {
        scala.Ordering.Implicits.sortedSetOrdering[SortedSet, TreeProjection].compare(formulaMultiplicites, that.formulaMultiplicites)
      }
    }
  }

}

object StackForestProjection {

  val empty: StackForestProjection = new StackForestProjection(SortedSet.empty,
                                                               SortedSet.empty,
                                                               SortedSet.empty)

  def fromPtrmodel(ac: AliasingConstraint[Var], inst: RuleInstance, model: Map[Var, Int], pointsTo: PointsTo): StackForestProjection = {
    type PredCall = (String, Seq[Int])
    val projectLoc: (Seq[PredCall], PredCall) = (inst.calls, (inst.pred.name, inst.predArgs))

    val imgS: Set[Int] = model.values.filter(_ > 0).toSet

    val univ = inst.locs.diff(imgS)
    val universals: SortedSet[BoundVar] = SortedSet.from((1 to univ.size).map(BoundVar.apply))

    val univRepl = univ.zip(universals).toMap
    val stackRepl_ = model.toSeq.map(t => (t._2, t._1)).toMap.map(kv => (kv._1, AliasingConstraint.largestAlias(ac, kv._2)))
    val stackRepl = stackRepl_.updated(0, NullConst)

    // sanity check
    require(univRepl.keySet.intersect(stackRepl.keySet).isEmpty)

    val r = new StackForestProjection(SortedSet(),
                                      universals,
                                      SortedSet.from(Seq(
                                        projections.TreeProjection(projectLoc._1.map({
                                          case (predName, args) =>
                                            Atom.PredicateCall(predName, args.map(i => univRepl.getOrElse(i, stackRepl(i))))
                                        }).sorted, Atom.PredicateCall(projectLoc._2._1, projectLoc._2._2.map(i => univRepl.getOrElse(i, stackRepl(i))))))))

    r
  }

  private def formulaFlatMap[A](formula: Iterable[TreeProjection], f: PredicateCall => Iterable[A]): Iterable[A] = {
    formula.flatMap({ case TreeProjection(calls, call) =>
      calls.flatMap(f) ++ f(call)
    })
  }

  def boundVariables(formula: Iterable[TreeProjection]): Set[BoundVar] = formulaFlatMap(formula, _.boundVars).toSet

  def freeVariables(formula: Iterable[TreeProjection]): Set[FreeVar] = formulaFlatMap(formula, _.freeVars).toSet.asInstanceOf[Set[FreeVar]]

  def varSeq(formula: SortedSet[TreeProjection]): Seq[Var] = {
    formula.toSeq.flatMap(tp => tp.allholepreds.flatMap(_.varSeq) ++ tp.rootpred.varSeq)
  }

  def composition(left: StackForestProjection, right: StackForestProjection): Set[StackForestProjection] = {
    //    val r = if (left.compare(right) <= 0)
    //      allRescopings(left, right).filter(_.isDelimited(sid)).flatMap(sfp => sfp.deriveGreedy /*.incl(sfp) TODO*/)
    //    else
    //      allRescopings(right, left).filter(_.isDelimited(sid)).flatMap(sfp => sfp.deriveGreedy /*.incl(sfp) TODO*/)
    //    val r = allRescopings(left, right).flatMap(sfp => sfp.derivableSet /*.incl(sfp) TODO*/)

    //(allRescopings(left, right) union allRescopings(right, left)).flatMap(sfp => sfp.derivableSet /*.incl(sfp) TODO*/)

    (allRescopings(left, right) union allRescopings(right, left)).flatMap(_.derivableSet)
  }

  def allRescopings(left: StackForestProjection, right: StackForestProjection): Set[StackForestProjection] = {
    val existentials = SortedSet.from(BoundVar.from(1, left.guardedExistentials.size + right.guardedExistentials.size))

    val universal: Left[Unit, BoundVar] = Left(())

    def getCombinations2(currentUniversals: Seq[BoundVar], otherExistentials: Seq[BoundVar]): Seq[Seq[(BoundVar, Either[Unit, BoundVar])]] = {
      def loop(toAssign: Seq[BoundVar]): Seq[Seq[(BoundVar, Either[Unit, BoundVar])]] = toAssign match {
        case Seq() => Seq(Seq.empty)
        case head +: tail =>
          loop(tail).flatMap(assgn => ((head, universal) +: assgn) +: otherExistentials.map(ex => (head, Right(ex)) +: assgn))
      }

      loop(currentUniversals)
    }

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

    //    val leftCombinations = getCombinations(left, right, left.guardedExistentials.size + 1)
    val leftCombinations = getCombinations2(left.guardedUniversals.toSeq, right.guardedExistentials.toSeq.map(bv => BoundVar(bv.index + left.guardedExistentials.size)))
    //    val rightCombinations = getCombinations(right, left, 1)
    val rightCombinations = getCombinations2(right.guardedUniversals.toSeq, left.guardedExistentials.toSeq)

    def aux(max: Int, vars: Seq[Either[BoundVar, BoundVar]]): Seq[Seq[(Either[BoundVar, BoundVar], BoundVar)]] = {
      vars match {
        case Seq() => Seq(Seq())
        case head +: tail =>

          (for (i <- 1 to max) yield {
            aux(max, tail).map(s => (head, BoundVar(i)) +: s)
          }).flatten

      }
    }

    val r = (for (leftCombination <- leftCombinations;
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

        val leftRemapping: Substitution[Var] = Substitution.from(leftExistentials)
        val rightRemapping: Substitution[Var] = Substitution.from(rightExistentials ++
                                                                    (1 to right.guardedExistentials.size).map(i => (BoundVar(i), BoundVar(i + left.guardedExistentials.size)))
                                                                  )

        Seq(new StackForestProjection(existentials,
                                      SortedSet.from(BoundVar.from(1, leftUnivs.size + rightUnivs.size, existentials.size)),
                                      left.formula.map(_.substitute(leftRemapping)) ++ right.formula.map(_.substitute(rightRemapping))))
      } else
        combs.map(seq => {
          val seqOffset = seq.map({ case (value, boundVar) => (value, BoundVar(boundVar.index + existentials.size)) })
          val universalSet = SortedSet.from(seqOffset.map(_._2))
          val leftUnivMapping: Seq[(BoundVar, BoundVar)] = seqOffset.collect { case (Left(v), boundVar) => (v, boundVar) }
          val rightUnivMapping: Seq[(BoundVar, BoundVar)] = seqOffset.collect { case (Right(v), boundVar) => (v, boundVar) }

          val leftRemapping: Substitution[Var] = Substitution.from((leftExistentials ++ leftUnivMapping).filter(t => t._1 != t._2))
          val rightRemapping: Substitution[Var] = Substitution.from((rightExistentials ++
                                                                      rightUnivMapping ++
                                                                      (1 to right.guardedExistentials.size).map(i => (BoundVar(i), BoundVar(i + left.guardedExistentials.size)))).filter(t => t._1 != t._2))

          new StackForestProjection(existentials,
                                    universalSet,
                                    left.formula.map(_.substitute(leftRemapping)) ++ right.formula.map(_.substitute(rightRemapping)))
        })

    }).flatten.toSet

    r
  }
}

case class TreeProjection(allholepreds: Seq[GslFormula.Atom.PredicateCall], rootpred: GslFormula.Atom.PredicateCall) extends Ordered[TreeProjection] {

  Utils.debugRequire(Utils.isSorted(allholepreds))

  def substitute(subst: Substitution[Var]): TreeProjection = {
    TreeProjection(allholepreds.map(_.substitute(subst)).sorted, rootpred.substitute(subst))
  }

  def allRootArguments(sid: SID_btw): Seq[Var] = {
    allholepreds.map(p => p.args(sid.predicates(p.pred).predrootIndex)) :+ rootpred.args(sid.predicates(rootpred.pred).predrootIndex)
  }

  override def compare(that: TreeProjection): Int = {
    val res = scala.Ordering.Implicits.seqOrdering[Seq, PredicateCall].compare(allholepreds, that.allholepreds)
    //val res = Utils.compareLexicographically(allholepreds, that.allholepreds)
    if (res == 0)
      rootpred.compare(that.rootpred)
    else
      res
  }
}