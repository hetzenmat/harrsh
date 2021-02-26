package at.forsyte.harrsh.parsers

import at.forsyte.harrsh.GSL.GslFormula.Atom._
import at.forsyte.harrsh.GSL.GslFormula._
import at.forsyte.harrsh.GSL.{GslFormula, Query, SID, SymbolicHeap}
import at.forsyte.harrsh.parsers.GslParser.WhiteSpaceChar
import at.forsyte.harrsh.seplog.{FreeVar, NullConst, Var}
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

  def parseQuery: Rule1[Query] = rule {
    _WhiteSpace ~ _FormulaSection ~ _SidSection ~ EOI ~> ((tuple: (GslFormula, Boolean), sid: SID) => Query(tuple._1, sid, tuple._2))
  }

  def parseFormula: Rule1[GslFormula] = rule {
    _WhiteSpace ~ _SeparatingConjunction ~ EOI
  }

  def parseRule: Rule1[SID.Rule] = rule {
    _WhiteSpace ~ _Rule ~ EOI
  }

  def parseSymbolicHeap: Rule1[SymbolicHeap] = rule {
    _WhiteSpace ~ _SymbolicHeap ~ EOI
  }

  def parseSID: Rule1[SID] = rule {
    _WhiteSpace ~ _Sid ~ EOI
  }

  private def _FormulaSection: Rule1[(GslFormula, Boolean)] = rule {
    ws("query") ~ ws('{') ~ _SeparatingConjunction ~ ws('}') ~> ((formula: GslFormula) => (formula, false)) |
      ws("query") ~ ws('{') ~ _SeparatingConjunction ~ ws("|=") ~ _SeparatingConjunction ~ ws('}') ~> ((left: GslFormula, right: GslFormula) => (Negation(left, right), true))
  }

  private def _SidSection: Rule1[SID] = rule {
    ws("sid") ~ ws('{') ~ _Sid ~ ws('}')
  }

  /*_*/
  private def _Sid: Rule1[SID] = rule {
    zeroOrMore(_Rule) ~> ((rules: Seq[SID.Rule]) => SID.buildSID(rules))
  }

  /*_*/

  private def _Rule: Rule1[SID.Rule] = rule {
    _Identifier ~ ws("<=") ~ _SymbolicHeap ~> ((name: String, sh: SymbolicHeap) => SID.Rule(name, Seq.empty, sh)) |
      _Identifier ~ ws('(') ~ _QuantifiedVarList ~ ws(')') ~ ws("<=") ~ _SymbolicHeap ~>
        ((name: String, args: Seq[String], sh: SymbolicHeap) => SID.Rule(name, args, sh))
  }

  private def _SymbolicHeap: Rule1[SymbolicHeap] = rule {
    ws('∃') ~ oneOrMore(_Identifier) ~ ws('.') ~ oneOrMore(_SymbolicHeapAtom).separatedBy(ws('*')) ~>
      ((vars: Seq[String], atoms: Seq[Atom]) => SymbolicHeap.buildSymbolicHeap(vars, atoms)) |
      oneOrMore(_SymbolicHeapAtom).separatedBy(ws('*')) ~> ((atoms: Seq[Atom]) => SymbolicHeap.buildSymbolicHeap(Seq.empty, atoms))
  }

  private def _SymbolicHeapAtom: Rule1[Atom] = rule {
    _PointsTo | _PredicateCall | _Equality | _DisEquality | _Emp | ws('(') ~ _SymbolicHeapAtom ~ ws(')')
  }

  private def _SeparatingConjunction: Rule1[GslFormula] = rule {
    _Disjunction ~ oneOrMore(ws('*') ~ _Disjunction) ~> ((left, right) => SeparatingConjunction.from(left, right)) |
      _Disjunction
  }

  private def _Disjunction: Rule1[GslFormula] = rule {
    _Guarded ~ ws("""\/""") ~ _Guarded ~> ((left, right) => Disjunction(left, right)) |
      _Guarded
  }

  private def _Guarded: Rule1[GslFormula] = rule {
    _MagicWand | _Septraction | _Negation | _StandardConjunction
  }

  private def _MagicWand: Rule1[GslFormula] = rule {
    _MagicWandRight | _MagicWandLeft
  }

  private def _UnguardedMagicWand: Rule1[(GslFormula, GslFormula)] = rule {
    ws('(') ~ _StandardConjunction ~ ws("-*") ~ _StandardConjunction ~ ws(")") ~> ((left, right) => (left, right)) |
      ws('(') ~ _UnguardedMagicWand ~ ws(')')
  }

  private def _MagicWandRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ _UnguardedMagicWand ~> ((guard: GslFormula, tuple: (GslFormula, GslFormula)) => MagicWand(guard, tuple._1, tuple._2))
  }

  private def _MagicWandLeft: Rule1[GslFormula] = rule {
    _UnguardedMagicWand ~ _And ~ _StandardConjunction ~> ((tuple: (GslFormula, GslFormula), guard: GslFormula) => GslFormula.MagicWand(guard, tuple._1, tuple._2))
  }

  private def _Septraction: Rule1[GslFormula] = rule {
    _SeptractionRight | _SeptractionLeft
  }

  private def _UnguardedSeptraction: Rule1[(GslFormula, GslFormula)] = rule {
    ws('(') ~ _StandardConjunction ~ (ws("-o") | ws("-⊛")) ~ _StandardConjunction ~ ws(')') ~> ((left, right) => (left, right)) |
      ws('(') ~ _UnguardedSeptraction ~ ws(')')
  }

  private def _SeptractionRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ _UnguardedSeptraction ~> ((guard: GslFormula, tuple: (GslFormula, GslFormula)) => GslFormula.Septraction(guard, tuple._1, tuple._2))
  }

  private def _SeptractionLeft: Rule1[GslFormula] = rule {
    _UnguardedSeptraction ~ _And ~ _StandardConjunction ~> ((tuple: (GslFormula, GslFormula), guard: GslFormula) => GslFormula.Septraction(guard, tuple._1, tuple._2))
  }

  private def _Negation: Rule1[GslFormula] = rule {
    _NegationLeft | _NegationRight
  }

  private def _NegationRight: Rule1[GslFormula] = rule {
    _StandardConjunction ~ _And ~ ws("~") ~ _Atom ~> ((guard: GslFormula, negated: GslFormula) => GslFormula.Negation(guard, negated))
  }

  private def _NegationLeft: Rule1[GslFormula] = rule {
    ws("~") ~ _Atom ~ _And ~ _StandardConjunction ~> ((negated: GslFormula, guard: GslFormula) => GslFormula.Negation(guard, negated))
  }

  private def _StandardConjunction: Rule1[GslFormula] = rule {
    _Atom ~ _And ~ _Atom ~> ((left, right) => GslFormula.StandardConjunction(left, right)) |
      _Atom
  }

  private def _And: Rule0 = ws("""/\""")

  private def _Atom: Rule1[GslFormula] = rule {
    _Emp |
      _Equality |
      _DisEquality |
      _PointsTo |
      _PredicateCall |
      ws('(') ~ _SeparatingConjunction ~ ws(')')
  }

  private def _Emp: Rule1[Atom.Emp] = rule(ws("emp") ~ push(GslFormula.Atom.Emp()))

  private def _Equality: Rule1[Atom.Equality] = rule {
    _Var ~ (ws("=") ~ _Var) ~> ((left: Var, right: Var) => Equality(left, right))
  }

  private def _DisEquality: Rule1[Atom.DisEquality] = rule {
    _Var ~ (ws("!=") ~ _Var) ~> ((left: Var, right: Var) => DisEquality(left, right))
  }

  private def _PointsTo: Rule1[Atom.PointsTo] = rule {
    _Var ~ ws("->") ~ _Var ~> ((from: Var, to: Var) => GslFormula.Atom.PointsTo(from, Seq(to))) |
      _Var ~ ws("->") ~ _ParenList ~> ((from: Var, to: Seq[Var]) => GslFormula.Atom.PointsTo(from, to))
  }

  private def _PredicateCall: Rule1[Atom.PredicateCall] = rule {
    _Identifier ~ ws('(') ~ _VarList ~ ws(')') ~> ((pred: String, args: Seq[Var]) => GslFormula.Atom.PredicateCall(pred, args))
  }

  private def _ParenList: Rule1[Seq[Var]] = rule {
    ws('(') ~ _VarList ~ ws(')') | ws('<') ~ _VarList ~ ws('>')
  }

  private def _VarList: Rule1[Seq[Var]] = rule {
    oneOrMore(_Var).separatedBy(ws(','))
  }

  /*_*/
  private def _QuantifiedVarList: Rule1[Seq[String]] = rule {
    zeroOrMore(_QuantifiedVar).separatedBy(ws(','))
  }

  /*_*/

  private def _QuantifiedVar: Rule1[String] = rule {
    (!("null" | "nil")) ~ _Var ~> ((v: Var) => v.toString)
  }

  private def _Var: Rule1[Var] = rule {
    (!"emp") ~ _Identifier ~> ((s: String) => s match {
      case "null" | "nil" => NullConst
      case v => FreeVar(v)
    })
  }

  private def _Identifier: Rule1[String] = rule {
    capture((predicate(CharPredicate.Alpha) | '_') ~ zeroOrMore(predicate(CharPredicate.AlphaNum) | '_')) ~ _WhiteSpace
  }

  private def _WhiteSpace: Rule0 = rule(quiet(zeroOrMore(WhiteSpaceChar)))

  private def ws(s: String): Rule0 = rule(s ~ _WhiteSpace)

  private def ws(c: Char): Rule0 = rule(c ~ _WhiteSpace)
}

object GslParser {
  private val WhiteSpaceChar: CharPredicate = CharPredicate(" \n\r\t\f")
}
