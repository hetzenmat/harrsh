package at.forsyte.harrsh

import at.forsyte.harrsh.main.EntailmentQuery
import at.forsyte.harrsh.seplog.inductive.{Predicate, SidLike, SymbolicHeap}
import at.forsyte.harrsh.util.ToLatex._

package object converters {

  case class ConversionException(msg: String) extends Exception(msg)

  def sanitize(s: String): String = s.replace('α', 'y').replace("null","nil")

  trait EntailmentFormatConverter extends ((String, EntailmentQuery) => Seq[(String,String)])

  val ToLatexConverter: EntailmentFormatConverter = (filename: String, pr: EntailmentQuery) => Seq((filename+".tex", pr.toLatex))

  def pointerArities(sid: SidLike, lhs: SymbolicHeap, rhs: SymbolicHeap): Set[Int] = {
    val sidPtoArities = for {
      p <- sid.preds.toSet[Predicate]
      r <- p.bodySHs
      ptr <- r.pointers
    } yield ptr.to.length
    val queryPtoArities = for {
      sh <- Seq(lhs, rhs)
      ptr <- sh.pointers
    } yield ptr.to.length
    sidPtoArities ++ queryPtoArities
  }

}
