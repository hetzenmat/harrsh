package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.GslFormula.Atom.PredicateCall
import at.forsyte.harrsh.GSL.GslFormula.{Negation, SeparatingConjunction}
import at.forsyte.harrsh.parsers.GslParser
import at.forsyte.harrsh.seplog.{FreeVar, Var}
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.SortedSet
import scala.util.{Failure, Success}

class EntailmentTest extends AnyFlatSpec {

  object SIDs {
    private def get(s: String): SID = {
      new GslParser(s).parseSID.run() match {
        case Failure(f) => {
          println(f);
          fail()
        }
        case Success(sid) => sid
      }
    }

    val lseg: SID = get(
      """
        |lseg(x1,x2) <= x1 -> <x2>
        |lseg(x1,x2) <= ∃y.x1 -> (y) * lseg(y, x2)
        |ls(x1) <= x1 -> nil
        |ls(x1) <= ∃y.x1 -> (y) * ls(y)
        |""".stripMargin)

    val ls: SID = get(
      """
        |ls(x1) <= x1 -> nil
        |ls(x1) <= ∃y.x1 -> (y) * ls(y)
        |ptr1(x1,x2) <= x1 -> x2
        |""".stripMargin)

    val ptr1: SID = get(
      """
        |ptr1(x1,x2) <= x1 -> x2
        |""".stripMargin)
  }

  def parseFormula(s: String): GslFormula = {
    new GslParser(s).parseFormula.run() match {
      case Failure(f) =>
        println(f)
        fail(f)
      case Success(formula) => formula
    }
  }

  def toBtw(s: SID): SID_btw = s.toBtw match {
    case Left(value) => fail(value)
    case Right(value) => value
  }

  "ab" should "jf" in {
    val lseg = toBtw(SIDs.lseg)
    //val (x, y): (Var, Var) = (FreeVar("x"), FreeVar("y"))
    val (x1, x2): (Var, Var) = (FreeVar("x1"), FreeVar("x2"))
    val (a, b, c): (Var, Var, Var) = (FreeVar("a"), FreeVar("b"), FreeVar("c"))

    //val ac = AliasingConstraint(Seq(SortedSet.from(Seq(x1)), SortedSet.from(Seq(x2))), Map((x1, 0), (x2, 1)))
    val ac = new AliasingConstraint(Seq(SortedSet.from(Seq(a, x1)), SortedSet.from(Seq(b, x2)), SortedSet.from(Seq(c))), Map((a, 0), (x1, 0), (x2, 1), (b, 1), (c, 2)))


    //val ac = AliasingConstraint(Seq(SortedSet.from(Seq(x1, x2))), Map((x1, 0), (x2, 0)))

    //    val types = new PredicateTypes(lseg, Set(a, b, c)).unfold(lseg.predicates("lseg"), ac)
    //    types.foreach { f =>
    //      println(f)
    //    }

    val s = new TypeComputation(lseg, parseFormula("a -> a * a -> a")).types(
      new AliasingConstraint(Seq(SortedSet.from(Seq(a))), Map((a, 0))))

    s.foreach { t =>
      println(t)
    }

    //    println("==============")
    //
    //    val r = new TypeComputation(lseg, parseFormula("lseg(a, b) * lseg(b, c)")).types(
    //      AliasingConstraint(Seq(SortedSet.from(Seq(a)), SortedSet.from(Seq(b)), SortedSet.from(Seq(c))), Map((a, 0), (b, 1), (c, 2))))
    //    r.foreach { t =>
    //      println(t)
    //    }
  }

  "Type computation" should "correctly decide entailments" in {
    val left = parseFormula("lseg(a, b) * lseg(b, c)")
    val right = parseFormula("lseg(a, c)")

    val q = Query(Negation(left, right), SIDs.lseg, fromEntailment = true)

    println(q.isSatisfiable)
  }

  "Type computation" should "correctly decide entailments 2" in {
    val left = parseFormula("a -> b * a = c")
    val right = parseFormula("c -> b")

    val q = Query(Negation(left, right), SIDs.ptr1, fromEntailment = true)

    println(q.isSatisfiable)
  }

  "Type computation" should "correctly decide entailments 3" in {
    val left = parseFormula("a -> b /\\ a -> c")
    val right = parseFormula("a -> b * b = c")

    val q = Query(Negation(left, right), SIDs.ptr1, fromEntailment = true)

    println(q.isSatisfiable)
  }

  "Type computation" should "correctly decide entailments 4" in {
    val left = parseFormula("a -> b * ls(b)")
    val right = parseFormula("ls(a)")

    val q = Query(Negation(left, right), SIDs.ls, fromEntailment = true)

    println(q.isSatisfiable)
  }

  "Type computation" should "correctly decide entailments 5" in {
    val left = parseFormula("lseg(a, b) * b -> null")
    val right = parseFormula("ls(a)")

    val q = Query(Negation(left, right), SIDs.lseg, fromEntailment = true)

    println(q.isSatisfiable)
  }
}