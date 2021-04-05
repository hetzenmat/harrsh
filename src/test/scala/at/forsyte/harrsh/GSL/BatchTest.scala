package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.parsers.GslParser
import org.scalatest.flatspec.AnyFlatSpec

import java.io.File
import scala.io.Source
import scala.util.Success

class BatchTest extends AnyFlatSpec {

  def getFiles(dir: File): Seq[File] = {
    dir.listFiles(_.isFile).filter(_.getName.endsWith(".gsl")) ++ dir.listFiles(_.isDirectory).flatMap(getFiles)
  }

  "GSL satisfiability decision procedure" should "correctly decide problems in examples/GSL" in {
    val gslExamples = new File("examples/GSL")

    assert(gslExamples.exists() && gslExamples.isDirectory)

    val queries = getFiles(gslExamples)
      .map(Source.fromFile)
      .map(source => new GslParser(source.mkString).parseQuery.run())
      .collect({ case Success(value) => value })
      .filter(_.status.isDefined)

    queries.foreach { query =>
      if (query.fromEntailment) {
        query.entailmentHolds match {
          case Left(value) => fail(value)
          case Right(value) => assert(value == query.status.get)
        }
      } else {
        query.isSatisfiable match {
          case Left(value) => fail(value)
          case Right(value) => assert(value == query.status.get)
        }
      }
    }
  }
}
