package at.forsyte.harrsh.seplog

/**
  * Created by jkatelaa on 9/30/16.
  */
sealed trait PtrExpr extends Expr {

  override def toString = this match {
    case NullPtr() => "null"
    case PtrVar(id) => id
  }

  def getVar : Set[String] = this match {
    case NullPtr() => Set()
    case PtrVar(id) => Set(id)
  }

  def <(other : PtrExpr) : Boolean = (this, other) match {
    case (NullPtr(), NullPtr()) => false
    case (NullPtr(), _) => true
    case (_, NullPtr()) => false
    case (PtrVar(l), PtrVar(r)) => l < r
  }

  def renameVars(f : Renaming) : PtrExpr = this match {
    case n : NullPtr => n
    case PtrVar(id) => PtrVar(f(id))
  }

  def isVar : Boolean = this match {
    case _ : NullPtr=> false
    case _ : PtrVar => true
  }

}

case class NullPtr() extends PtrExpr

case class PtrVar(id : String) extends PtrExpr

object PtrExpr {

  def fromString(s : String) : PtrExpr = s match {
    case "null" => NullPtr()
    case "nil" => NullPtr()
    case _ => PtrVar(s)
  }

}