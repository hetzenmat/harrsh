
package at.forsyte.harrsh.GSL.query

import at.forsyte.harrsh.GSL.SID.SID_btw

object QueryContext {
  private var currentSID: SID_btw = _

  private[query] def setSID(sid_btw: SID_btw): Unit = {
    currentSID = sid_btw
  }

  @inline
  def getSid: SID_btw = currentSID
}
