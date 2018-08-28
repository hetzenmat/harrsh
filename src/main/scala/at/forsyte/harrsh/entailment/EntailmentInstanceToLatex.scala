package at.forsyte.harrsh.entailment

import at.forsyte.harrsh.seplog.Var
import at.forsyte.harrsh.seplog.Var.Naming
import at.forsyte.harrsh.seplog.inductive.PureAtom
import at.forsyte.harrsh.util.ToLatex

object EntailmentInstanceToLatex {

  val etypeToLatex: ToLatex[ExtensionType] = (a: ExtensionType, _: Naming) => extensionTypeToLatexLines(a).mkString("\n")

  object extensionTypeToLatexLines {

    // TODO: Less hacky latex conversion
    // TODO: Reduce code duplication with ForestsToLatex

    def apply(extensionType: ExtensionType): Stream[String] = {
      val ordered = extensionType.parts.toStream
      val tifpics = ordered.zipWithIndex.flatMap {
        case (tif, ix) =>
          val style = if (ix == 0) "" else {
            val bottomLeft = if (ordered(ix - 1).leaves.nonEmpty) s"tif${ix-1}_0" else s"tif${ix-1}_root"
              s"below=5mm of $bottomLeft"
          }
          treeInterfaceToLatexLines(tif, "tif" + ix, style)
      }
      inTikzPic(tifpics, Some(EtStyleClass))
    }

    def inTikzPic(lines: Stream[String], style: Option[String] = None): Stream[String] = {
      val styleString = style.map('[' + _ + ']').getOrElse("")
      Stream(s"\\begin{tikzpicture}$styleString") ++ lines ++ Stream("\\end{tikzpicture}")
    }

    def treeInterfaceToLatexLines(tif: TreeInterface, tifId: String, rootStyle: String): Stream[String] = {
      val rootId = tifId + "_root"
      val diseqId = tifId + "_diseqs"
      val fitId = tifId + "_fit"

      val TreeInterface(root, leaves, usageInfo, diseqs) = tif
      val rootTikz = nodeLabelToLatexLines(root, usageInfo, rootId, rootStyle)
      val diseqsTikz = diseqsToTikz(diseqs, rootId, diseqId, s"right=of $rootId")

      val leavesTikz = leaves.toStream.zipWithIndex.flatMap {
        case (leaf, ix) =>
          val position = if (ix == 0) s"below=2mm of $rootId" else s"right=of ${tifId}_${ix-1}"
          nodeLabelToLatexLines(leaf, usageInfo, tifId + "_" + ix, s"missing,$position")
      }
      val leafIds = (0 until leaves.size) map (tifId + "_" + _)
      val nodeIds = Seq(rootId, diseqId) ++ leafIds
      val fitConstraint = nodeIds.map("(" + _ + ")").mkString(" ")

      val fitTikz = Stream(s"\\node[draw=black!50, fit={$fitConstraint}] ($fitId) {};")

      rootTikz ++ diseqsTikz ++ leavesTikz ++ fitTikz
    }

    private val varsToMath = (v: Var) => Naming.indexify(Naming.DefaultNaming)(v) match {
      case "null" => "\\nil"
      case other => other
    }

    private def diseqsToTikz(diseqs: DisequalityTracker, tifRootId: String, nodeId: String, style: String): Stream[String] = {
      val disEqsToLatex = (deqs: Set[PureAtom]) => if (deqs.isEmpty) "---" else deqs.map(a => s"$$${varsToMath(a.l)} \\neq ${varsToMath(a.r)}$$").mkString(", ")

      if (diseqs.ensured.nonEmpty || diseqs.missing.nonEmpty) {
        val ensuredLabel = s"Guaranteed: ${disEqsToLatex(diseqs.ensured)}"
        val missingLabel = s"Missing: ${disEqsToLatex(diseqs.missing)}"
        val missingStyle = if (diseqs.missing.nonEmpty) s"$MissingStyleClass," else ""
        Stream(s"\\node[$NodeLabelStyleClass,$style,${missingStyle}right=2mm of $tifRootId] ($nodeId) {\\footnotesize $ensuredLabel \\nodepart{two} \\footnotesize $missingLabel};")
      } else {
        Stream.empty
      }
    }

    private def nodeLabelToLatexLines(nodeLabel: NodeLabel, usageInfo: VarUsageByLabel, nodeId: String, style: String): Stream[String] = {
      val tikzNodeLabel = nodeLabel.symbolicHeapLabel

      val (pred, subst) = (nodeLabel.pred, nodeLabel.subst)
      // TODO: Annotate with usage info
      val pairs = (pred.params, subst.toSeq).zipped.map {
        case (from, to) => varsToMath(from) + " \\rightarrow " + to.map(varsToMath).mkString(",")
      }
      val substLatex = '$' + pairs.mkString(";") + '$'

      Stream(s"\\node[$NodeLabelStyleClass,$style] ($nodeId) {$tikzNodeLabel \\nodepart{two} \\footnotesize $substLatex};")
    }
  }

  object entailmentCheckerResultToLatex {

    def apply(aut: EntailmentAutomaton, reachable: Set[(String, EntailmentAutomaton.State)]): String = {
      val isFinal = (s: EntailmentAutomaton.State) => aut.isFinal(s)
      val content = statesToLatex(reachable, isFinal)
      latexTemplate.replace(ContentPlaceholder, content)
    }

    def statesToLatex(states: Set[(String, EntailmentAutomaton.State)], isFinal: EntailmentAutomaton.State => Boolean): String = {
      val statesByPred: Map[String, Set[EntailmentAutomaton.State]] = states.groupBy(_._1).mapValues(pairs => pairs.map(_._2))
      val lines = Stream("\\begin{itemize}") ++ statesByPred.toStream.flatMap(pair => Stream("\\item") ++ predToLatex(pair._1, pair._2, isFinal)).map(indent) ++ Stream("\\end{itemize}")
      lines.mkString("\n")
    }

    def predToLatex(pred: String, states: Set[EntailmentAutomaton.State], isFinal: EntailmentAutomaton.State => Boolean): Stream[String] = {
      Stream(s"Reachable states for \\texttt{$pred}:", "\\begin{itemize}") ++ states.toStream.flatMap(s => stateToLatex(s, isFinal)).map(indent) ++ Stream("\\end{itemize}")
    }

    def stateToLatex(state: EntailmentAutomaton.State, isFinal: EntailmentAutomaton.State => Boolean): Stream[String] = {
      val finalStr = if (isFinal(state)) "\\textbf{FINAL} " else ""
      val header = s"\\item ${finalStr}State with params ${state.orderedParams.mkString(", ")} and extension types:"

      val etsStream = if (state.ets.isEmpty) {
        Stream("\\item No consistent extension type (failure state)")
      } else {
        Stream("\\item Extension types:", "\\begin{enumerate}") ++ state.ets.toStream.flatMap(et => Stream("\\item") ++ extensionTypeToLatexLines(et)) ++ Stream("\\end{enumerate}")
      }

      Stream(header, "\\begin{itemize}") ++ etsStream ++ Stream("\\end{itemize}")
    }

    private def indent(s : String) = "  " + s

  }

  private val EtStyleClass = "et"
  private val NodeLabelStyleClass = "utnode"
  private val MissingStyleClass = "missing"
  private val ContentPlaceholder = "CONTENT"

  private val latexTemplate = s"""\\documentclass{article}
                                |\\usepackage[a2paper, landscape]{geometry}
                                |
                                |\\newcommand{\\nil}{\\ensuremath{\\textnormal{\\textbf{null}}}}
                                |
                                |\\usepackage{tikz}
                                |\\usetikzlibrary{backgrounds,arrows,shapes,positioning,fit}
                                |
                                |\\tikzset{$EtStyleClass/.style={background rectangle/.style={fill=orange!30}, show background rectangle}}
                                |\\tikzset{$NodeLabelStyleClass/.style={draw,rectangle split, rectangle split
                                |    parts=2,inner sep=2pt}}
                                |\\tikzset{$MissingStyleClass/.style={fill=red!30}}
                                |
                                |\\begin{document}
                                |
                                |$ContentPlaceholder
                                |
                                |\\end{document}""".stripMargin('|')

}
