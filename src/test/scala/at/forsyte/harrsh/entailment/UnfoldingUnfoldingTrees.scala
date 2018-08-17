package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.ExampleSIDs

object UnfoldingUnfoldingTrees {

  def main(args: Array[String]) : Unit = {
    val sid = ExampleSIDs.Tll
    val pred = sid.preds.head
    val (base, rec) = (pred.rules(0), pred.rules(1))
    val ut = UnfoldingTree.singleton(sid, pred)
    println(ut)
    println(ut.unfold(ut.root, sid, base))
    val recTree = ut.unfold(ut.root, sid, rec)
    println(recTree)
    val recBaseTree = recTree.unfold(recTree.children(recTree.root)(1), sid, base)
    println(recBaseTree)
    val recBaseBaseTree = recBaseTree.unfold(recBaseTree.children(recTree.root)(0), sid, base)
    println(recBaseBaseTree)
  }

}