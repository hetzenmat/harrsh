package at.forsyte.harrsh.seplog.inductive

import at.forsyte.harrsh.seplog.Renaming

/**
  * Created by jkatelaa on 10/3/16.
  */
case class SymbolicHeap(pure : Seq[PureAtom], spatial: Seq[SpatialAtom], qvars : Seq[String]) {

  def this(pure : Seq[PureAtom], spatial: Seq[SpatialAtom]) = this(pure, spatial, Seq())

  def this(spatial: Seq[SpatialAtom]) = this(Seq(), spatial, Seq())

  override def toString = {
    val prefix = qvars map ("\u2203"+_) mkString " "
    val spatialString = spatial.mkString(" * ")
    val pureString = if (pure.isEmpty) "" else pure.mkString(" : {", ", ", "}")
    prefix + (if (prefix.isEmpty) "" else " . ") + spatialString + pureString
  }

  def hasPointer: Boolean = spatial.exists(_.isInstanceOf[PointsTo])

  def calledPreds: Seq[String] = spatial filter (_.isInductiveCall) map (_.getPredicateName.get)

  def getCalls : Seq[PredCall] = spatial filter (_.isInductiveCall) map (_.asInstanceOf[PredCall])

  def pointers : Seq[PointsTo] = spatial filter (_.isInstanceOf[PointsTo]) map (_.asInstanceOf[PointsTo])

  def equalities : Seq[PtrEq] = pure filter (_.isInstanceOf[PtrEq]) map (_.asInstanceOf[PtrEq])

  def ptrComparisons : Seq[PureAtom] = pure filter (a => a.isInstanceOf[PtrEq] || a.isInstanceOf[PtrNEq])

  def withoutCalls : SymbolicHeap = copy(spatial = spatial.filter(!_.isInductiveCall))

  def renameVars(f : Renaming) = {
    // Rename bound variables if applicable
    val (qvarsRenamed, extendedF) : (Seq[String], Renaming) = qvars.foldRight((Seq[String](), f))({
      case (v, (seq, intermediateF)) =>
        val extended = intermediateF.addBoundVarWithOptionalAlphaConversion(v)
        (extended(v) +: seq, extended)
    })

    SymbolicHeap(pure map (_.renameVars(extendedF)), spatial map (_.renameVars(extendedF)), qvarsRenamed)
  }

  def getVars : Set[String] = qvars.toSet ++ pure.flatMap(_.getVars) ++ spatial.flatMap(_.getVars)

}

object SymbolicHeap {

  def apply(pure : Seq[PureAtom], spatial: Seq[SpatialAtom]) = new SymbolicHeap(pure, spatial)

  def apply(spatial: Seq[SpatialAtom]) = new SymbolicHeap(spatial)

  def combineHeaps(phi : SymbolicHeap, psi : SymbolicHeap) : SymbolicHeap = {
    val SymbolicHeap(pure, spatial, qvars) = phi
    // Rename bound variables in the right formula that clash with the left formula
    val SymbolicHeap(pure2, spatial2, qvars2) = psi.renameVars(Renaming.clashAvoidanceRenaming(qvars))
    val combinedVars = qvars ++ qvars2
    SymbolicHeap(pure ++ pure2, spatial ++ spatial2, combinedVars)
  }

  def combineAllHeaps(heaps : Seq[SymbolicHeap]) : SymbolicHeap = heaps.foldRight(SymbolicHeap(Seq())){
    (sh, shAcc) => combineHeaps(sh, shAcc)
  }

}
