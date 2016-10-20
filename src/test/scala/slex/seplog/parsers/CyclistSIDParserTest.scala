package slex.seplog.parsers

import slex.test.{SlexTableTest}

/**
  * Created by jkatelaa on 10/20/16.
  */
class CyclistSIDParserTest extends SlexTableTest {

  import CyclistSIDParser._

  val Success = true
  val Failure = false

  val inputs = Table(
    ("parser", "input", "result"),
    (parseAtomSeq, "a=f * I1355_1(a,b,c,d,e,f)", Success),
    (parseAtomSeq, "a!=f * I1355_1(a,b,c,d,e,f)", Success),
    (parseAtomSeq, "nil!=e * e->a' * I1317_1(a,b,c,d,e,a')", Success),
    (parseRule, "nil!=d * d->a' * I166_1(a,b,c,d,a') => I046(a,b,c,d)", Success),
    (parseSID, fullExample, Success)
  )

  property ("The Cyclist SID parser should work") {
    forAll(inputs) {
      (parser, input, expectedResult) =>
        val parseResult = parseAll(parser, input)

        info(""+parseResult)

        if (expectedResult) {
          parseResult.successful should be (expectedResult)
        }
    }
  }


  private def fullExample = """ls {
    nil=a => ls(a) |
      nil!=a * I001_1(a) => ls(a)
  } ;

  I209166 {
    I40239_0(a,b,c,d,e,f,g,j) => I209166(a,b,c,d,e,f,g,h,i,j)
  } ;

  I209106 {
    nil!=i * i->a' * I209166_1(a,b,c,d,e,f,g,h,i,a') => I209106(a,b,c,d,e,f,g,h,i)
  } ;

  I209107 {
    I40306_0(a,b,c,d,e,f,g,i) => I209107(a,b,c,d,e,f,g,h,i)
  } ;

  I209073 {
    nil=i * I209107_1(a,b,c,d,e,f,g,h,i) => I209073(a,b,c,d,e,f,g,h,i) |
      nil!=i * I209106_1(a,b,c,d,e,f,g,h,i) => I209073(a,b,c,d,e,f,g,h,i)
  } ;

  I40305 {
    nil!=h * h->a' * I209073_1(a,b,c,d,e,f,g,h,a') => I40305(a,b,c,d,e,f,g,h)
  } ;

  I60989 {
    I40306_0(i,b,c,d,e,f,g,h) => I60989(a,b,c,d,e,f,g,h,i)
  } ;

  I40341 {
    nil!=a * a->a' * I60989_1(a,b,c,d,e,f,g,h,a') => I40341(a,b,c,d,e,f,g,h)
  } ;

  I40306 {
    nil=a => I40306(a,b,c,d,e,f,g,h) |
      nil!=a * I40341_1(a,b,c,d,e,f,g,h) => I40306(a,b,c,d,e,f,g,h)
  } ;

  I40239 {
    nil=h * I40306_1(a,b,c,d,e,f,g,h) => I40239(a,b,c,d,e,f,g,h) |
      nil!=h * I40305_1(a,b,c,d,e,f,g,h) => I40239(a,b,c,d,e,f,g,h)
  } ;

  I40109 {
    nil!=g * g->a' * I40239_1(a,b,c,d,e,f,g,a') => I40109(a,b,c,d,e,f,g)
  } ;

  I40192 {
    I40110_0(h,b,c,d,e,f,g) => I40192(a,b,c,d,e,f,g,h)
  } ;

  I40179 {
    nil!=a * a->a' * I40192_1(a,b,c,d,e,f,g,a') => I40179(a,b,c,d,e,f,g)
  } ;

  I40110 {
    a=g => I40110(a,b,c,d,e,f,g) |
      a!=g * I40179_1(a,b,c,d,e,f,g) => I40110(a,b,c,d,e,f,g)
  } ;

  I40085 {
    nil=g * I40110_1(a,b,c,d,e,f,g) => I40085(a,b,c,d,e,f,g) |
      nil!=g * I40109_1(a,b,c,d,e,f,g) => I40085(a,b,c,d,e,f,g)
  } ;

  I39957 {
    nil!=f * f->a' * I40085_1(a,b,c,d,e,f,a') => I39957(a,b,c,d,e,f)
  } ;

  I40046 {
    I39958_0(a,g,c,d,e,f) => I40046(a,b,c,d,e,f,g)
  } ;

  I40035 {
    nil!=b * b->a' * I40046_1(a,b,c,d,e,f,a') => I40035(a,b,c,d,e,f)
  } ;

  I39958 {
    b=f => I39958(a,b,c,d,e,f) |
      b!=f * I40035_1(a,b,c,d,e,f) => I39958(a,b,c,d,e,f)
  } ;

  I39937 {
    nil=f * I39958_1(a,b,c,d,e,f) => I39937(a,b,c,d,e,f) |
      nil!=f * I39957_1(a,b,c,d,e,f) => I39937(a,b,c,d,e,f)
  } ;

  I182 {
    nil!=e * e->a' * I39937_1(a,b,c,d,e,a') => I182(a,b,c,d,e)
  } ;

  I11677 {
    I183_0(a,b,f,d,e) => I11677(a,b,c,d,e,f)
  } ;

  I7185 {
    nil!=c * c->a' * I11677_1(a,b,c,d,e,a') => I7185(a,b,c,d,e)
  } ;

  I183 {
    c=e => I183(a,b,c,d,e) |
      c!=e * I7185_1(a,b,c,d,e) => I183(a,b,c,d,e)
  } ;

  I166 {
    nil=e * I183_1(a,b,c,d,e) => I166(a,b,c,d,e) |
      nil!=e * I182_1(a,b,c,d,e) => I166(a,b,c,d,e)
  } ;

  I046 {
    nil!=d * d->a' * I166_1(a,b,c,d,a') => I046(a,b,c,d)
  } ;

  I063 {
    I047_0(e,b,c,d) => I063(a,b,c,d,e)
  } ;

  I056 {
    nil!=a * a->a' * I063_1(a,b,c,d,a') => I056(a,b,c,d)
  } ;

  I047 {
    nil=a => I047(a,b,c,d) |
      nil!=a * I056_1(a,b,c,d) => I047(a,b,c,d)
  } ;

  I034 {
    nil=d * I047_1(a,b,c,d) => I034(a,b,c,d) |
      nil!=d * I046_1(a,b,c,d) => I034(a,b,c,d)
  } ;

  I021 {
    nil!=c * c->a' * I034_1(a,b,c,a') => I021(a,b,c)
  } ;

  I022 {
    I008_0(b,c) => I022(a,b,c)
  } ;

  I013 {
    nil=c * I022_1(a,b,c) => I013(a,b,c) |
      nil!=c * I021_1(a,b,c) => I013(a,b,c)
  } ;

  I007 {
    nil!=b * b->a' * I013_1(a,b,a') => I007(a,b)
  } ;

  I008 {
    emp => I008(a,b)
  } ;

  I003 {
    nil=b * I008_1(a,b) => I003(a,b) |
      nil!=b * I007_1(a,b) => I003(a,b)
  } ;

  I001 {
    nil!=a * a->a' * I003_1(a,a') => I001(a)
  }"""

}
