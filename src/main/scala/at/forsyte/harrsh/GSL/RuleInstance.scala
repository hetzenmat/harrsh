package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.SID.SID

case class RuleInstance(pred: SID.Predicate[SymbolicHeapBtw], predArgs: Seq[Int], from: Int, to: Seq[Int], calls: Seq[(String, Seq[Int])]) {

  val locs: Set[Int] = Set.from((predArgs :+ from) ++ to ++ calls.flatMap(_._2)).filter(_ > 0)
}
