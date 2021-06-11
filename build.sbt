
name := "harrsh"

version := "1.0"

scalaVersion := "2.13.6"

// scalacOptions ++= Seq("-Xmax-classfile-name","78")

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.3.0"

libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.15.1" % "test"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.0"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.3" % "test"

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.3.2"

libraryDependencies += "org.antlr" % "antlr4-runtime" % "4.7"

libraryDependencies += "org.parboiled" %% "parboiled" % "2.2.1"

scalacOptions ++= Seq("-deprecation",
                      "-feature",
                      //"-optimize",
                      "-explaintypes",
                      "-Xdev",
                      "-Xlint:_")

//test in assembly := {}

//import sbtassembly.AssemblyPlugin.defaultShellScript
//assemblyOption in assembly := (assemblyOption in assembly).value.copy(prependShellScript = Some(defaultShellScript))
//assemblyJarName in assembly := s"${name.value}"
//ainClass in assembly := Some("at.forsyte.harrsh.main.Harrsh")
//mainClass in assembly := Some("at.forsyte.harrsh.main.SlCompMode")

//enablePlugins(JmhPlugin)