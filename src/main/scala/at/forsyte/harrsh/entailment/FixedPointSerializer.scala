package at.forsyte.harrsh.entailment

case class FixedPointSerializer(ei: EntailmentInstance, markFinalProfiles: Boolean) {

  private val sid = ei.rhs.sid
  private val rhsTopLevelConstraint = ei.rhs.topLevelConstraint

  def apply(statesByPred: Map[String, Set[EntailmentProfile]]): String =
    List(List("FIXED_POINT {") ++ statesByPred.flatMap(pair => serializePred(pair._1, pair._2)).map(indent) ++ List("}")).mkString("\n")

  def apply(profss: Iterable[Set[EntailmentProfile]]): String =
    (List("SEQUENCE_OF_PROFILE_SETS {") ++ profss.flatMap(serializeSetOfProfiles).map(indent) ++ List("}")).mkString("\n")

  private def indent(s : String): String = "  " + s

  private def serializePred(pred: String, profs: Set[EntailmentProfile]): List[String] = {
    List(s"PRED $pred {") ++ profs.flatMap(serializeProfile).map(indent) ++ List("}")
  }

  private def serializeSetOfProfiles(profs: Set[EntailmentProfile]): List[String] = {
    List("SET_OF_PROFILES {") ++ profs.flatMap(serializeProfile).map(indent) ++ List("}")
  }

  private def serializeProfile(profile: EntailmentProfile): LazyList[String] = {
    (LazyList("PROFILE {",
      s"  FVS: ${profile.params.toSeq.sorted.mkString(", ")}")
      ++ Some("  ACCEPTING").filter(_ => markFinalProfiles).filter(_ => profile.isFinal(sid, rhsTopLevelConstraint))
      ++ Some("  SHARED: " + profile.sharedConstraints)
      ++ serializeContent(profile) ++ LazyList("}"))
  }

  private def serializeContent(profile: EntailmentProfile): LazyList[String] = profile match {
    case ProfileOfDecomps(decomps, _, _) => serializeDecomps(decomps)
    case ProfileOfNondecomposableModels(constraints, _) =>
      LazyList(indent("NO CONSISTENT DECOMPOSITION"), indent(constraints.toString))
  }

  private def serializeDecomps(decomps: Set[ContextDecomposition]): LazyList[String] = {
    decomps.flatMap(serializeContextDecomposition).map(indent).to(LazyList)
  }

  private def serializeContextDecomposition(decomp: ContextDecomposition): LazyList[String] = {
    val decompStrs = decomp.parts.toList map (_.toString)
    val indent = "       "
    val fst = if (decompStrs.nonEmpty) decompStrs.head else "empty"
    val tail = if (decompStrs.nonEmpty) decompStrs.tail else Seq.empty
    val constraintsStr = indent + decomp.constraints
    LazyList(s"Decomp($fst,") ++ tail.map(indent + _ + ",") ++ LazyList(constraintsStr + ")")
  }

}
