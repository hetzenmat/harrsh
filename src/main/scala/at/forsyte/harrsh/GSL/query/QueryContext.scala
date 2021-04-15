
package at.forsyte.harrsh.GSL.query

import at.forsyte.harrsh.GSL.Env
import at.forsyte.harrsh.GSL.SID.SID_btw
import at.forsyte.harrsh.GSL.projections.optimized.TreeProjection

object QueryContext {
  private var currentSID: SID_btw = _

  private[query] def setSID(sid_btw: SID_btw): Unit = {
    currentSID = sid_btw
  }

  @inline
  def getRootArgument(predicateCall: TreeProjection.PredicateCall): Int =
    predicateCall(currentSID.predicates(Env.predReverse(predicateCall.head)).predrootIndex + 1)

  @inline
  def sid: SID_btw = currentSID
}
