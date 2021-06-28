package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.bimap.mutable

object Env {
  private[this] val predBiMap: mutable.BiMap[String, Int] = mutable.BiMap.empty
  private[this] val varBiMap: mutable.BiMap[String, Int] = mutable.BiMap.empty
  private[this] var predCounter: Int = 0
  private[this] var varCounter: Int = 0

  @inline def predForward(pred: String): Int =
    predBiMap.synchronized {
      if (predBiMap.forwardDefinedAt(pred))
        predBiMap.forward(pred)
      else {
        predCounter += 1
        predBiMap.add(pred, predCounter)
        predCounter
      }
    }

  @inline def predReverse: Int => String = predBiMap.reverse

  @inline def varForward(variable: String): Int =
    varBiMap.synchronized {
      if (varBiMap.forwardDefinedAt(variable))
        varBiMap.forward(variable)
      else {
        varCounter += 1
        varBiMap.add(variable, varCounter)
        varCounter
      }
    }

  @inline def varReverse: Int => String = varBiMap.reverse
}
