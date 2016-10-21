package at.forsyte.harrsh.seplog.inductive

import at.forsyte.harrsh.main.SlexLogging
import at.forsyte.harrsh.seplog.{PtrExpr, Renaming}

/**
  * Created by jkatelaa on 10/3/16.
  */
sealed trait PureAtom extends SepLogAtom with SlexLogging {

  override def isSpatial = false

  override def isPure = true

  override def isSymbolicHeap = true

  override def toSymbolicHeap = Some(SymbolicHeap(Seq(this), Seq(), Seq()))

  override def renameVars(f: Renaming): PureAtom = this match {
    case t : True => t
    case PtrEq(l, r) => PtrEq(l.renameVars(f), r.renameVars(f))
    case PtrNEq(l, r) => PtrNEq(l.renameVars(f), r.renameVars(f))
  }

  def getVars : Set[String] = {
    def toSet(l : PtrExpr, r : PtrExpr) : Set[String] = {
      if (l.isVar && r.isVar) Set(l.toString, r.toString)
      else if (l.isVar) Set(l.toString)
      else if (r.isVar) Set(r.toString)
      else Set.empty
    }

    this match {
      case True() => Set()
      case PtrEq(l, r) =>
        toSet(l,r)
      //l.getVar union r.getVar
      case PtrNEq(l, r) =>
        toSet(l,r)
      //l.getVar union r.getVar
    }
  }

}

case class True() extends PureAtom {
  override def toString = "true"
}

case class PtrEq(l : PtrExpr, r : PtrExpr) extends PureAtom {
  override def toString = l + " \u2248 " + r
}

case class PtrNEq(l : PtrExpr, r : PtrExpr) extends PureAtom {
  override def toString = l + " \u2249 " + r
}