package at.forsyte.harrsh.GSL

import scala.math.Ordering.Tuple2

/*, missingKeyFunction: K => Option[V] = Function.const(None), missingValueFunction: V => Option[K] = Function.const(None)*/

object BiMap {
  def from[K, V](tuples: Seq[(K, V)])(implicit ord1: Ordering[K], ord2: Ordering[V]) = new BiMap(tuples.sorted)
}

class BiMap[K, V] private(val tuples: Seq[(K, V)] /*, val missingKeyFunction: K => Option[V], val missingValueFunction: V => Option[K]*/) {

  require(tuples.map(_._1).toSet.size == tuples.size)
  require(tuples.map(_._2).toSet.size == tuples.size)

  val forwardMap: Map[K, V] = tuples.toMap
  val reverseMap: Map[V, K] = tuples.map(_.swap).toMap

  def forward(key: K): V = {
    //    if (forwardMap.contains(key))
    forwardMap(key)
    //    else
    //      missingKeyFunction(key).get
  }

  def reverse(value: V): K = {
    //    if (reverseMap.contains(value))
    reverseMap(value)
    //    else
    //      missingValueFunction(value).get
  }

  override def hashCode(): Int = tuples.hashCode()

  override def equals(obj: Any): Boolean = obj match {
    case value: BiMap[K, V] =>
      tuples == value.tuples
    case _ =>
      false
  }
}
