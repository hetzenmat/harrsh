package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.seplog.{BoundVar, FreeVar, Var}

case class TreeInterface private(root: NodeLabel, leaves: Set[AbstractLeafNodeLabel], usageInfo: VarUsageByLabel, pureConstraints: PureConstraintTracker) {

  assert(NodeLabel.noRedundantPlaceholders(labels), s"There are redundant placeholders in $this")

  lazy val labels: Seq[NodeLabel] = Seq[NodeLabel](root) ++ leaves

  lazy val placeholders: Set[PlaceholderVar] = substs.flatMap(_.placeholders).toSet

  lazy val boundVars: Set[BoundVar] = substs.flatMap(_.boundVars).toSet

  private lazy val substs = labels map (_.subst)

  override def toString: String = {
    val leavesString = if (leaves.isEmpty) "empty" else leaves.mkString(",")
    val usageStr = usageInfo.map{
      case (vs, usage) => vs.mkString(",") + "->" + usage
    }.mkString("; ")
    val ensuredStr = pureConstraints.ensured.mkString(",")
    val missingStr = pureConstraints.missing.mkString(",")
    s"TI(root = $root; leaves = $leavesString; usage = { $usageStr }; ensured = { $ensuredStr }; missing = { $missingStr })"
  }

  def isConcrete: Boolean = leaves.isEmpty

  def hasConsistentPureConstraints: Boolean = pureConstraints.isConsistent

  def hasNamesForRootParams: Boolean = labels.forall{
    label =>
      val rootParamIndex = label.pred.rootParamIndex.get
      val labelingVars: Set[Var] = label.subst.toSeq(rootParamIndex)
      labelingVars.exists(v => v.isFreeNonNull && !PlaceholderVar.isPlaceholder(v))
  }

  def asExtensionType: ExtensionType = ExtensionType(Set(this))

  def nonPlaceholderFreeVars: Set[FreeVar] = {
    substs.flatMap(_.freeNonNullVars).filterNot(PlaceholderVar.isPlaceholder).toSet
  }

  def updateSubst(f: SubstitutionUpdate, convertToNormalform: Boolean): TreeInterface = {
    TreeInterface(root.update(f),
      leaves map (_.update(f)),
      VarUsageByLabel.update(usageInfo, f),
      pureConstraints.update(f),
      convertToNormalform)
  }

  def dropVarsFromPureConstraints(varsToDrop: Set[Var]): TreeInterface = {
    TreeInterface(root, leaves, usageInfo, pureConstraints.dropVars(varsToDrop), convertToNormalform = false)
  }
}

object TreeInterface {

  implicit val canComposeTreeInterfaces: CanCompose[TreeInterface] = CanComposeTreeInterface.canComposeTreeInterfaces

  def apply(root: NodeLabel, leaves: Set[AbstractLeafNodeLabel], usageInfo: VarUsageByLabel, pureConstraints: PureConstraintTracker, convertToNormalform: Boolean): TreeInterface = {
    if (convertToNormalform) {
      normalFormConversion(root, leaves, usageInfo, pureConstraints)
    } else {
      new TreeInterface(root, leaves, usageInfo, pureConstraints)
    }
  }

  def normalFormConversion(root: NodeLabel, leaves: Set[AbstractLeafNodeLabel], usageInfo: VarUsageByLabel, pureConstraints: PureConstraintTracker): TreeInterface = {
    val dropper = SubstitutionUpdate.redundantPlaceholderDropper(Set(root) ++ leaves)
    val rootAfterDropping = root.update(dropper)
    val leavesAfterDropping = leaves map (_.update(dropper))
    val usageInfoAfterDropping = VarUsageByLabel.update(usageInfo, dropper)
    val diseqsAfterDropping = pureConstraints.update(dropper)

    val establishNormalForm = NodeLabel.labelsToPlaceholderNormalForm(Seq(rootAfterDropping) ++ leavesAfterDropping)

    new TreeInterface(
      rootAfterDropping.update(establishNormalForm),
      leavesAfterDropping map (_.update(establishNormalForm)),
      VarUsageByLabel.update(usageInfoAfterDropping, establishNormalForm),
      diseqsAfterDropping.update(establishNormalForm))
  }

  def isInNormalForm(tif: TreeInterface): Boolean = {
    NodeLabel.noRedundantPlaceholders(tif.labels) && PlaceholderVar.noGapsInPlaceholders(tif.placeholders)
  }

  def haveNoConflicts(tif1: TreeInterface, tif2: TreeInterface): Boolean = {
    (tif1.placeholders intersect tif2.placeholders).isEmpty
  }

}