package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.GSL.query.QueryContext
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}

import scala.collection.{MapView, mutable}

/**
  * Like in a conversation with Jens: only compute types for the aliasing constraints whose domain equals to variables of the formula or predicate
  *
  * Representation of a type: Map from aliasing constraints to set of phi-types (unsat => set of types is empty)
  *
  * Fixed-point computation of predicates with worklist algorithm?
  */
class SmartTypeComputation {
  private type LookupFunction = (String, AliasingConstraint[Var]) => Set[PhiType]

  private val finished: mutable.Set[(String, AliasingConstraint[Var])] = mutable.Set.empty
  private val predicateTypes: mutable.Map[String, mutable.Map[AliasingConstraint[Var], Set[PhiType]]] = mutable.Map.empty
  private val worklist: mutable.Set[(String, AliasingConstraint[Var])] = mutable.Set.empty
  private val nonRecursiveTypes: mutable.Map[(SymbolicHeapBtw, AliasingConstraint[Var]), Set[PhiType]] = mutable.Map.empty
  private val lookup: LookupFunction = (p, a) => predicateTypes.getOrElse(p, mutable.Map.empty).getOrElse(a, mutable.Map.empty)

  private val undefined: Nothing = throw new IllegalStateException("Trying to evaluate 'undefined'")

  private def pop[T](s: mutable.Set[T]): T = {
    val r = s.head
    s.remove(r)

    r
  }

  def ptypes(sh: SymbolicHeapBtw, ac: AliasingConstraint[Var], lookup: LookupFunction): Set[PhiType] = ???

  def getTypes(predName: String, sid: SID_btw = QueryContext.getSid): MapView[AliasingConstraint[Var], Set[PhiType]] = {

    val pred = sid.predicates(predName)

    val aliasingConstraints = AliasingConstraint
      .allAliasingConstraints(pred.freeVars.incl(NullConst))

    // Precompute types of non-recursive symbolic heaps
    for (ac <- aliasingConstraints;
         sh <- pred.rules if !sh.isRecursive) {
      if (!nonRecursiveTypes.contains((sh, ac))) {
        nonRecursiveTypes.put((sh, ac), ptypes(sh, ac, (_, _) => undefined))
      }
    }

    // Populate worklist
    aliasingConstraints
      .foreach(ac => worklist.add((predName, ac)))

    val worklistHistory = mutable.Set.empty[(String, AliasingConstraint[Var])]

    while (worklist.nonEmpty) {
      val (predName, ac) = pop(worklist)
      worklistHistory.add((predName, ac))
      val currentPredicate = sid.predicates(predName)

      if (!finished.contains((predName, ac))) {
        val pred = sid.predicates(predName)

        val types = (for (rule <- pred.rules) yield {
          if (rule.isRecursive)
            ptypes(rule, ac, lookup)
          else
            nonRecursiveTypes((rule, ac))
        }).toSet.flatten

        assert(lookup(predName, ac).subsetOf(types))

        if (types.size > lookup(predName, ac)) {
          if (!predicateTypes.contains(predName)) predicateTypes.put(predName, mutable.Map.empty)
          predicateTypes(predName).put(ac, types)

          val acPlaceholders = ac.rename(currentPredicate.argsSeq.zipWithIndex.map({
            case (v, idx) => (v, FreeVar("?" + (idx + 1)): Var)
          }).toMap)

          // TODO: insert values into the worklist that depend on (predName, ac)
          for ((pn, p) <- sid.predicates;
               rule <- p.rules;
               call <- rule.calls.filter(pc => pc.pred == predName)) {
            val correspondence = call.varSeq.zip(currentPredicate.argsSeq.zipWithIndex).filter({
              case (NullConst, _) => true
              case (_: FreeVar, _) => true
              case _ => false
            })

            // check if the correspondence is not compatible with the current AC, i.e., if (0, x) is present but
            // in the current AC it does not hold that 0 ~ x
            if (correspondence.forall({
              case (NullConst, (v, _)) => ac =:= (NullConst, v)
              case _ => true
            })) {
              val subst = correspondence.map({ case (arg, (_, idx)) => (FreeVar("?" + (idx + 1)) : Var, arg)}).toMap
              val baseAC = acPlaceholders.rename(subst).restricted(subst.values.toSet.incl(NullConst))

              assert(baseAC.domain.contains(NullConst))

              baseAC.allExtensionsIt(p.freeVars.diff(baseAC.domain)).foreach(ac => {
                assert(ac.domain == p.freeVars.incl(NullConst))

                worklist.add((pn, ac))
              })
            }
          }
        }
      }
    }

    // TODO: Add everything from worklist history to finished?

    predicateTypes(predName).view
  }
}