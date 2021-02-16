package at.forsyte.harrsh.GSL

case class RuleInstance(predName: String, predArgs: Seq[Int], from: Int, to: Seq[Int], calls: Seq[(String, Seq[Int])]) {

}
