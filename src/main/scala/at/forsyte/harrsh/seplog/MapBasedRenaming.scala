package at.forsyte.harrsh.seplog

/**
  * Created by jkatelaa on 10/17/16.
  */
case class MapBasedRenaming(map : Map[Var, Var]) extends Renaming {

  override lazy val codomain: Set[Var] = map.values.toSet

  override def apply(x: Var): Var = map.getOrElse(x, x)

  override def extendWith(k: Var, v: Var): Renaming = MapBasedRenaming(map + (k -> v))

  override def toString = "[" + map.map(p => Var.toDefaultString(p._1)+"->"+Var.toDefaultString(p._2)).mkString(",") + "]"

  override def isDefinedAt(s: Var): Boolean = map.isDefinedAt(s)
}
