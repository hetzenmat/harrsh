package at.forsyte.harrsh.seplog

import at.forsyte.harrsh.seplog.inductive.{PointsTo, PureAtom}
import at.forsyte.harrsh.util.{StringUtils, ToLatex}

import scala.collection.immutable.SortedSet

/**
  * Created by jens on 11/2/16.
  */

sealed trait Var extends Ordered[Var] {

  def isFreeNonNull: Boolean

  def isFree: Boolean

  def isBound: Boolean

  def isNull: Boolean

  /**
    * Construct atom that asserts the equality of `this` with `other`
    */
  def =:=(other: Var): PureAtom = PureAtom(this, other, isEquality = true)

  /**
    * Construct atom that asserts the disequality of `this` with `other`
    */
  def =/=(other: Var): PureAtom = PureAtom(this, other, isEquality = false)

  def ->(other: Var): PointsTo = PointsTo(this, other)

  def ->(other2: (Var, Var)): PointsTo = PointsTo(this, Seq(other2._1, other2._2))

  def ->(other3: (Var, Var, Var)): PointsTo = PointsTo(this, Seq(other3._1, other3._2, other3._3))

  def ->(other4: (Var, Var, Var, Var)): PointsTo = PointsTo(this, Seq(other4._1, other4._2, other4._3, other4._4))

  def ->(other5: (Var, Var, Var, Var, Var)): PointsTo = PointsTo(this, Seq(other5._1, other5._2, other5._3, other5._4, other5._5))

  def rename(f: Renaming): Var = f(this)

  override def compare(other: Var): Int = (this, other) match {
    case (BoundVar(i), BoundVar(j)) => i - j
    case (Multiplicity(i), Multiplicity(j)) => i - j
    case (BoundVar(_), NullConst) => -1
    case (BoundVar(_), FreeVar(_)) => -1
    case (NullConst, FreeVar(_)) => -1
    case (NullConst, NullConst) => 0
    case (NullConst, _) => 1
    case (FreeVar(m), FreeVar(n)) => m compare n
    case (FreeVar(_), _) => 1
    case (Multiplicity(_), _) => -1
    case (_, Multiplicity(_)) => 1
  }

}

case class Multiplicity(amount: Int) extends Var {
  override def isFreeNonNull: Boolean = false

  override def isFree: Boolean = false

  override def isBound: Boolean = true

  override def isNull: Boolean = false
}

case class FreeVar(name: String) extends Var {

  assert(!Var.isNullString(name))

  override def isFreeNonNull: Boolean = true

  override def isFree: Boolean = true

  override def isBound: Boolean = false

  override def isNull: Boolean = false

  override def toString: String = name
}

case object NullConst extends Var {
  override def isFreeNonNull: Boolean = false

  override def isFree: Boolean = true

  override def isBound: Boolean = false

  override def isNull: Boolean = true

  override def toString: String = Var.NullString
}

case class BoundVar(index: Int) extends Var {
  assert(index > 0)

  override def isFreeNonNull: Boolean = false

  override def isFree: Boolean = false

  override def isBound: Boolean = true

  override def isNull: Boolean = false

  override def toString: String = Var.BoundVarPrefix + index

}

object BoundVar {

  def from(start: Int, to: Int, offset: Int = 0): IndexedSeq[BoundVar] = {
    fromRange((start + offset) to (to + offset))
  }

  def fromRange(range: Range): IndexedSeq[BoundVar] = {
    range.map(i => BoundVar(i))
  }
}

object Var {

  val NullString = "null"
  val NilString = "nil"
  val BoundVarPrefix = "\u03b1"
  val FreeVarDefaultPrefix = "x"

  implicit def ord[T <: Var]: Ordering[T] = Ordering.fromLessThan(_ < _)

  private val latexReplacements = Seq(
    "\u03b1" -> "\\alpha",
    "__" -> "\\beta_",
    NilString -> "\\nil",
    NullString -> "\\nil"
    )

  implicit val varToLatex: ToLatex[Var] = (v: Var, naming: Naming) => {
    StringUtils.literalReplacements(latexReplacements, naming(v))
  }

  def indexedVarToLatex(v: Var): String = varToLatex.toLatex(v, Naming.indexify(Naming.DefaultNaming))

  def indexedVarsToLatex(vs: Iterable[Var]): String = {
    val mathVars = vs map indexedVarToLatex
    if (mathVars.size == 1) mathVars.head else mathVars.mkString("\\{", ",", "\\}")
  }

  def isNullString(s: String): Boolean = {
    s == NullString || s == NilString
  }

  def stringTofreeOrNullVar(s: String): Var = {
    if (isNullString(s)) NullConst else FreeVar(s)
  }

  def defaultFV(index: Int): FreeVar = FreeVar(FreeVarDefaultPrefix + index)

  def freshFreeVar(usedFVIdents: Set[Var]): FreeVar = {
    var candidate = usedFVIdents.size + 1
    var candidateVar = defaultFV(candidate)
    while (usedFVIdents.contains(candidateVar)) {
      candidate += 1
      candidateVar = defaultFV(candidate)
    }
    candidateVar
  }

  def freshFreeVars(usedFVIdents: Set[Var], numFreshFV: Int): Seq[FreeVar] = {
    if (numFreshFV == 0) {
      Seq.empty
    } else {
      val newFV = freshFreeVar(usedFVIdents)
      newFV +: freshFreeVars(usedFVIdents + newFV, numFreshFV - 1)
    }
  }

  def getFvSeq(length: Int): Seq[FreeVar] = {
    (1 to length) map defaultFV
  }

  def getNextUnusedBoundVar(vars: Iterable[Var]): BoundVar = {
    try {
      val maxUsed = Var.boundVars(SortedSet.empty[Var] ++ vars).map(_.index).max
      BoundVar(maxUsed + 1)
    } catch {
      case _: UnsupportedOperationException => BoundVar(1)
    }
  }

  // TODO: Remove code duplication. Generic solution?
  def boundVars(vars: SortedSet[Var]): SortedSet[BoundVar] = {
    vars.collect {
      case v: BoundVar => v
    }
  }

  def freeNonNullVars(vars: SortedSet[Var]): SortedSet[FreeVar] = {
    vars.collect {
      case v: FreeVar => v
    }
  }

  def freeNonNullVars(vars: Seq[Var]): Seq[FreeVar] = {
    vars.collect {
      case v: FreeVar => v
    }
  }

  def containsNull(vars: Iterable[Var]): Boolean = vars.exists(_ == NullConst)

  @inline def maxOf(vars: Iterable[Var]): Var = vars.max

  @inline def minOf(vars: Iterable[Var]): Var = vars.min

  type Naming = Var => String
  type UnNaming = String => Var

  object Naming {

    lazy val DefaultNaming: Naming = v => v.toString

    lazy val DefaultHarrshNaming: Naming = v => v.toString.map {
      c => if (c == BoundVarPrefix.head) 'y' else c
    }

    def mkNaming(freeVars: Seq[String], boundVars: SortedSet[BoundVar], boundVarNames: Seq[String]): Naming = {
      val freeVarNaming = freeVars map (v => (FreeVar(v), v))
      val boundVarNaming = boundVars zip boundVarNames
      Map.empty[Var, String] ++ freeVarNaming ++ boundVarNaming ++ Map(NullConst -> NullConst.toString)
    }

    def mkUnNaming(freeVars: Seq[String], boundVars: Seq[String]): UnNaming = {
      val freeVarNaming = freeVars map (v => (v, FreeVar(v)))
      val boundVarNaming = boundVars.zipWithIndex map (p => (p._1, BoundVar(p._2 + 1)))
      Map.empty[String, Var] ++ freeVarNaming ++ boundVarNaming ++ Map(NullConst.toString -> NullConst)
    }

    /**
      * Return new naming where all integer suffixes are turned into LaTeX subscripts
      *
      * @param naming Original naming
      * @return updated naming
      */
    def indexify(naming: Naming): Naming = {
      v => StringUtils.indexifyNumbers(naming(v))
    }
  }

}
