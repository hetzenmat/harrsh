package at.forsyte.harrsh.parsers

import at.forsyte.harrsh.main.{HarrshLogging, ProblemStatus, Query, RefinementQuery}
import at.forsyte.harrsh.refinement.{AutomatonTask, RunSat}
import at.forsyte.harrsh.seplog.inductive.Sid
import at.forsyte.harrsh.util.{IOUtils, StringUtils}

object QueryParser extends HarrshLogging {

  case class ParseException(msg: String) extends Exception(msg)

  object FileExtensions {
    val Cyclist = "defs"
    val HarrshSid = "sid"
    val HarrshEntailment = "hrs"
    val SlComp = "smt2"

    private val sidExtensions = Set(HarrshSid, Cyclist)

    def isSidExtension(ext: String): Boolean = sidExtensions contains ext
  }

  def apply(fileName: String): Query = {
    StringUtils.splitOffExtension(fileName) match {
      case None => tryAll(fileName)
      case Some((_, ext)) => tryParserForExtension(fileName, ext)
    }
  }

  /**
    * Parse file into SID
    */
  def getSidFromFile(fileName : String) : Sid = {
    val parser = if (fileName.endsWith(FileExtensions.Cyclist)) {
      logger.debug("File ends in .defs, will assume cyclist format")
      SidParsers.CyclistSidParser
    } else {
      logger.debug("Assuming standard SID format")
      SidParsers.DefaultSidParser
    }

    val content = IOUtils.readFile(fileName)

    parser.runOnSid(content) match {
      case Some(sid) =>
        sid
      case None =>
        IOUtils.printWarningToConsole("Parsing the SID failed, exiting")
        throw ParseException(s"Parsing file '$fileName' as SID failed")
    }
  }

  private def tryParserForExtension(fullFileName: String, ext: String): Query = {
    ext match {
      case FileExtensions.SlComp =>
        slcomp.parseFileToQuery(fullFileName).getOrElse{
          throw ParseException(s"Parsing file '$fullFileName' as SLCOMP-Input failed")
        }
      case FileExtensions.HarrshEntailment =>
        EntailmentParsers.parseHarrshEntailmentFormat(IOUtils.readFile(fullFileName)).map(_.setFileName(fullFileName)).getOrElse{
          throw ParseException(s"Parsing file '$fullFileName' as Harrsh Entailment Query failed")
        }
      case e if FileExtensions.isSidExtension(e) =>
        RefinementQuery(fullFileName, RunSat)
      case _ =>
        tryAll(fullFileName)
    }
  }

  private def tryAll(fileName: String): Query = {
    val parseOptions: LazyList[Option[Query]] = LazyList(
      EntailmentParsers.parseHarrshEntailmentFormat(fileName).map(_.setFileName(fileName)),
      slcomp.parseFileToQuery(fileName),
      SidParsers.CombinedSidParser.runOnSid(IOUtils.readFile(fileName)) map (sid => RefinementQuery(sid, Some(RunSat), ProblemStatus.Unknown, Some(fileName)))
    )
    parseOptions.find(_.isDefined).flatten.getOrElse{
      throw ParseException(s"Could not parse '$fileName' with any parser.")
    }
  }

}
