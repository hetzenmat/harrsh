package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.bimap.mutable
import at.forsyte.harrsh.seplog.{NullConst, Var}

object Env {
  private[this] val predBiMap: mutable.BiMap[String, Int] = mutable.BiMap.empty
  private[this] val varBiMap: mutable.BiMap[Var, Int] = mutable.BiMap.empty
  varBiMap.add(NullConst, 0)
  private[this] var predCounter: Int = 0
  private[this] var varCounter: Int = 0

  @inline def predForward(pred: String): Int =
    if (predBiMap.forwardDefinedAt(pred)) predBiMap.forward(pred)
    else predBiMap.synchronized {
      predCounter += 1
      predBiMap.add(pred, predCounter)
      predCounter
    }

  @inline def predReverse: Int => String = predBiMap.reverse

  @inline def varForward(variable: Var): Int =
    if (varBiMap.forwardDefinedAt(variable)) varBiMap.forward(variable)
    else varBiMap.synchronized {
      varCounter += 1
      varBiMap.add(variable, varCounter)
      varCounter
    }

  @inline def varReverse: Int => Var = varBiMap.reverse
}
