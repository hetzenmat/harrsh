package at.forsyte.harrsh.seplog.inductive

import at.forsyte.harrsh.seplog.{NullConst, SepLogSyntax, Var}

import scala.collection.immutable.SortedSet

/**
  * Created by jkatelaa on 10/20/16.
  */
trait SepLogAtom extends SepLogSyntax {
  def getVars : SortedSet[Var]

  final def getNonNullVars : SortedSet[Var] = getVars - NullConst
}
