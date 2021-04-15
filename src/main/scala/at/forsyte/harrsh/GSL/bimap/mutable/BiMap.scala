package at.forsyte.harrsh.GSL.bimap.mutable

import scala.collection.mutable

/*, missingKeyFunction: K => Option[V] = Function.const(None), missingValueFunction: V => Option[K] = Function.const(None)*/

object BiMap {
  def empty[K, V] = new BiMap[K, V]
}

class BiMap[K, V] private {

  private val forwardMap: mutable.Map[K, V] = mutable.Map.empty
  private val reverseMap: mutable.Map[V, K] = mutable.Map.empty

  def forward: K => V = forwardMap.apply

  def reverse: V => K = reverseMap.apply

  def forwardDefinedAt: K => Boolean = forwardMap.isDefinedAt

  def reverseDefinedAt: V => Boolean = reverseMap.isDefinedAt

  def add(k: K, v: V): Unit = {
    forwardMap.get(k) match {
      case Some(value) => require(value == v)
      case None => forwardMap.put(k, v)
    }

    reverseMap.get(v) match {
      case Some(value) => require(value == k)
      case None => reverseMap.put(v, k)
    }
  }

  override def hashCode(): Int = forwardMap.hashCode()

  override def equals(obj: Any): Boolean = obj match {
    case value: BiMap[K, V] => value.forwardMap == forwardMap
    case _ => false
  }
}
