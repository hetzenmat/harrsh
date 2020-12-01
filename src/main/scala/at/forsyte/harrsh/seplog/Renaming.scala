package at.forsyte.harrsh.seplog

/**
  * Created by jkatelaa on 10/17/16.
  */
trait Renaming {

  /**
    * Applies the renaming to the given variable, returning the variable itself if it is not defined at the given var
    * @param s
    * @return
    */
  def apply(s : Var) : Var

  /**
    * Adds a renaming from k to v to the given renaming
    * @param k Key
    * @param v Renamed value
    * @return Extended renaming
    */
  def extendWith(k : Var, v: Var) : Renaming

  def codomain : Set[Var]

  def isDefinedAt(s : Var) : Boolean

  /**
    * Keeps only those renaming pairs that satisfy p
    * @param p
    * @return Renaming with !p pairs removed
    */
  def filter(p : (Var,Var) => Boolean) : Renaming

  def toPairs: Seq[(Var,Var)]

  private final def freshName(v: Var): Var =
    if (!codomain.contains(v)) {
      v
    } else if (v.isBound) {
      freshName(BoundVar(v.asInstanceOf[BoundVar].index + 1))
    } else {
      Var.freshFreeVar(codomain)
    }

  final def addBoundVarWithOptionalAlphaConversion(varid: Var) : Renaming = {
    // Note: We always add an entry for the varid, even if no renaming is necessary
    // This ensures that there are no repeated qvars in the combination of multiple sub-heaps with the same quantified vars
    extendWith(varid, freshName(varid))
  }

}

object Renaming {

  /**
    * Creates a Renaming function whose domain consists of dummy values and whose codomain is equal to the given set of varClashes.
    * When passed as argument to symbolic heap renaming, this will in effect rename all bound variables that appear in varClashes to fresh names.
    * @param varClashes Set of potentially clashing variables
    * @return Renaming with codomain varClashes
    */
  def clashAvoidanceRenaming(varClashes : Iterable[Var]) : Renaming = {
    val entries = varClashes.zipWithIndex map {
      case (v,i) => (BoundVar(Integer.MIN_VALUE + i), v)
    }
    fromPairs(entries)
  }

  def fromPairs(pairs : Iterable[(Var,Var)]) : Renaming = fromMap(Map() ++ pairs)

  def fromMap(mapOfPairs : Map[Var,Var]) : Renaming = MapBasedRenaming(mapOfPairs)

  private case class MapBasedRenaming(map : Map[Var, Var]) extends Renaming {

    override lazy val codomain: Set[Var] = map.values.toSet

    override def apply(x: Var): Var = map.getOrElse(x, x)

    override def extendWith(k: Var, v: Var): Renaming = MapBasedRenaming(map.updated(k, v))

    override def toString(): String = "[" + map.map(p => s"${p._1}->${p._2}").mkString(",") + "]"

    override def isDefinedAt(s: Var): Boolean = map.isDefinedAt(s)

    override def filter(p: (Var, Var) => Boolean): Renaming = MapBasedRenaming(map.filter(p.tupled))

    override def toPairs: Seq[(Var,Var)] = map.toSeq
  }

}
