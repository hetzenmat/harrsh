
package at.forsyte.harrsh.GSL.query

import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.GSL.bimap.{immutable, mutable}
import at.forsyte.harrsh.GSL.projections.optimized.TreeProjection
import at.forsyte.harrsh.seplog.{NullConst, Var}

import scala.collection.SortedSet

object QueryContext {
  private var currentSID: SID_btw = _

  private var predBiMap: immutable.BiMap[String, Int] = _
  private var varBiMap: mutable.BiMap[Var, Int] = _
  private var nextVar: Int = _

  private[query] def setSID(sid_btw: SID_btw): Unit = {
    currentSID = sid_btw
    setPredBiMap(SortedSet.from(currentSID.predicates.keySet))
    varBiMap = mutable.BiMap.empty
    varBiMap.add(NullConst, 0)
    nextVar = 1
  }

  private[query] def setPredBiMap(predicates: SortedSet[String]): Unit = {
    predBiMap = immutable.BiMap.from(predicates.zipWithIndex.map(t => (t._1, t._2 + 1)))
  }

  @inline def predForward: String => Int = predBiMap.forward

  @inline def predReverse: Int => String = predBiMap.reverse

  @inline def varForward: Var => Int = varBiMap.forward

  @inline def varReverse: Int => Var = varBiMap.reverse

  @inline
  def getRootArgument(predicateCall: TreeProjection.PredicateCall): Int =
    predicateCall(currentSID.predicates(predBiMap.reverse(predicateCall.head)).predrootIndex + 1)

  @inline
  def sid: SID_btw = currentSID
}
