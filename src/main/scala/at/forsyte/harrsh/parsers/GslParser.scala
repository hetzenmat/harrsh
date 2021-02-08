package at.forsyte.harrsh.parsers

import at.forsyte.harrsh.GSL.GslFormula
import at.forsyte.harrsh.GSL.GslFormula._
import at.forsyte.harrsh.parsers.GslParser.WhiteSpaceChar
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}
import org.parboiled2
import org.parboiled2._

/**
  * Created by Matthias Hetzenberger on 2021-02-07
  *
  * A parser for GSL formulae
  *
  * Precedence:
  * Separating Conjunction
  * Disjunction
  * Guarded: (Magic Wand
  * Septraction
  * Negation)
  * Conjunction
  * Atom
  */
class GslParser(val input: ParserInput) extends Parser {

  override def errorTraceCollectionLimit = 1000

  def parseFormula: Rule1[GslFormula] = rule {
    _SeparatingConjunction ~ parboiled2.EOI
  }

  def _SeparatingConjunction: Rule1[GslFormula] = rule {
    (_Disjunction ~ ws('*') ~ _Disjunction ~> ((left, right) => SeparatingConjunction(left, right))) |
      _Disjunction
  }

  def _Disjunction: Rule1[GslFormula] = rule {
    (_Guarded ~ ws("""\/""") ~ _Guarded ~> ((left, right) => Disjunction(left, right))) |
      _Guarded
  }

  def _Guarded: Rule1[GslFormula] = rule {
    _MagicWand | _Septraction | _Negation | _StandardConjunction
  }

  def _MagicWand: Rule1[GslFormula] = rule {
    _MagicWandRight | _MagicWandLeft
  }

  def _UnguardedMagicWand: Rule1[(GslFormula, GslFormula)] = rule {
    (ws('(') ~ _StandardConjunction ~ ws("-*") ~ _StandardConjunction ~ ws(")") ~> ((left, right) => (left, right))) |
      (ws('(') ~ _UnguardedMagicWand ~ ws(')'))
  }

  def _MagicWandRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ _UnguardedMagicWand ~> ((guard: GslFormula, tuple: (GslFormula, GslFormula)) => MagicWand(guard, tuple._1, tuple._2))
  }

  def _MagicWandLeft: Rule1[GslFormula] = rule {
    _UnguardedMagicWand ~ _And ~ _StandardConjunction ~> ((tuple: (GslFormula, GslFormula), guard: GslFormula) => GslFormula.MagicWand(guard, tuple._1, tuple._2))
  }

  def _Septraction: Rule1[GslFormula] = rule {
    _SeptractionRight | _SeptractionLeft
  }

  def _UnguardedSeptraction: Rule1[(GslFormula, GslFormula)] = rule {
    (ws('(') ~ _StandardConjunction ~ (ws("-o") | ws("-⊛")) ~ _StandardConjunction ~ ws(')') ~> ((left, right) => (left, right))) |
      (ws('(') ~ _UnguardedSeptraction ~ ws(')'))
  }

  def _SeptractionRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ _UnguardedSeptraction ~> ((guard: GslFormula, tuple: (GslFormula, GslFormula)) => GslFormula.Septraction(guard, tuple._1, tuple._2))
  }

  def _SeptractionLeft: Rule1[GslFormula] = rule {
    _UnguardedSeptraction ~ _And ~ _StandardConjunction ~> ((tuple: (GslFormula, GslFormula), guard: GslFormula) => GslFormula.Septraction(guard, tuple._1, tuple._2))
  }

  def _Negation: Rule1[GslFormula] = rule {
    _NegationLeft | _NegationRight
  }

  def _NegationRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ ws("~") ~ _Atom ~> ((guard: GslFormula, negated: GslFormula) => GslFormula.Negation(guard, negated))
  }

  def _NegationLeft: Rule1[GslFormula] = rule {
    ws("~") ~ _Atom ~ _And ~ _StandardConjunction ~> ((negated: GslFormula, guard: GslFormula) => GslFormula.Negation(guard, negated))
  }

  def _StandardConjunction: Rule1[GslFormula] = rule {
    (_Atom ~ _And ~ _Atom ~> ((left, right) => GslFormula.StandardConjunction(left, right))) |
      _Atom
  }

  def _And: Rule0 = ws("""/\""")

  def _Atom: Rule1[GslFormula] = rule {
    _Emp |
      _Equality |
      _DisEquality |
      _PointsTo |
      _PredicateCall |
      (ws('(') ~ _SeparatingConjunction ~ ws(')'))
  }

  def _Emp: Rule1[GslFormula] = rule(ws("emp") ~ push(GslFormula.Atom.Emp()))

  def _Equality: Rule1[GslFormula] = rule {
    _Var ~ (ws("=") ~ _Var) ~> ((left, right) => GslFormula.Atom.Equality(left, right))
  }

  def _DisEquality: Rule1[GslFormula] = rule {
    _Var ~ (ws("!=") ~ _Var) ~> ((left, right) => GslFormula.Atom.DisEquality(left, right))
  }

  def _PointsTo: Rule1[GslFormula] = rule {
    _Var ~ ws("->") ~ _Var ~> ((from: Var, to: Var) => GslFormula.Atom.PointsTo(from, Seq(to))) |
      _Var ~ ws("->") ~ _ParenList ~> ((from: Var, to: Seq[Var]) => GslFormula.Atom.PointsTo(from, to))
  }

  def _PredicateCall: Rule1[GslFormula] = rule {
    _Predicate ~ ws('(') ~ _VarList ~ ws(')') ~> ((pred: String, args: Seq[Var]) => GslFormula.Atom.PredicateCall(pred, args))
  }

  def _ParenList: Rule1[Seq[Var]] = rule {
    (ws('(') ~ _VarList ~ ')') | (ws('<') ~ _VarList ~ ws('>'))
  }

  def _VarList: Rule1[Seq[Var]] = rule {
    oneOrMore(_Var).separatedBy(ws(','))
  }

  def _Predicate: Rule1[String] = rule {
    capture((predicate(CharPredicate.Alpha) | '_') ~ zeroOrMore(predicate(CharPredicate.AlphaNum) | '_')) ~ _WhiteSpace
  }

  def _Var: Rule1[Var] = rule {
    (!"emp") ~ capture((predicate(CharPredicate.Alpha) | '_') ~ zeroOrMore(predicate(CharPredicate.AlphaNum) | '_')) ~ _WhiteSpace ~> ((s: String) => s match {
      case "null" | "nil" => NullConst
      case v => FreeVar(v)
    })
  }

  def _WhiteSpace: Rule0 = rule(quiet(zeroOrMore(WhiteSpaceChar)))

  def ws(s: String): Rule0 = rule(s ~ _WhiteSpace)

  def ws(c: Char): Rule0 = rule(c ~ _WhiteSpace)
}

object GslParser {
  val WhiteSpaceChar: CharPredicate = CharPredicate(" \n\r\t\f")
}
