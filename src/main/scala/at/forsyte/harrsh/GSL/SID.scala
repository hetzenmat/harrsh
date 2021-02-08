package at.forsyte.harrsh.GSL

/**
  * Created by Matthias Hetzenberger on 2021-02-08
  *
  * Represent an SID
  */
case class SID(rules: Map[String, Seq[SymbolicHeap]]) {
}

object SID {

  case class Rule(name: String, args: Seq[String], body: SymbolicHeap) {
    if (args.toSet.size != args.size)
      throw RuleException("Repeated arguments")

    if (!body.freeVars.map(_.toString).subsetOf(args.toSet))
      throw RuleException("Free variables are not subset of rule arguments")
  }

  def apply(rules: Seq[Rule]): SID =
    SID(rules.foldLeft(Map.empty[String, Seq[SymbolicHeap]]) { (map, rule) =>
      map.updatedWith(rule.name) {
        case None => Some(Seq(rule.body))
        case Some(seq) => Some(seq.appended(rule.body))
      }
    })
}

final case class RuleException(private val message: String = "",
                               private val cause: Throwable = None.orNull)
  extends Exception(message, cause)
