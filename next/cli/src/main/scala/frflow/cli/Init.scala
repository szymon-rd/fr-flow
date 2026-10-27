package frflow.cli

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.api.FrFlowApi
import frflow.cli.text.ReportText
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardOpenOption}

/** A new project in this build: `sbt "frflowNextInit toy --as NAME"`. It writes an empty FrModel and its main object,
  * a class for its examples, and the project's line in build.sbt (its examples run by `sbt toy/test`); with `--as`,
  * the developer's own act, it lists the developer's key as the first decider (`.frflow/deciders`, signed by it). A
  * layer on top (`frflow.agent.Init`) makes the same project with its extensions in the main object.
  */
object Init:
  private val Name = "[a-z][a-z0-9]*".r

  // A plain main: it runs inside sbt (`runMain`), where an effect runtime would warn about sbt's threads.
  def main(args: Array[String]): Unit = run(args.toList, None, name => List(
    s"next: sbt reload; propose the root statements in examples/$name, then see where they stand:",
    s"  sbt \"$name/run status\""))

  /** Writes the project named in `args` (`NAME [--as DECIDER]`), with `extensions` (Scala, as the main object passes
    * them); prints `next`.
    */
  def run(args: List[String], extensions: Option[String], next: String => List[String]): Unit = args match
    case List(name)              => made(name, None, extensions, next)
    case List(name, "--as", who) => made(name, Some(who), extensions, next)
    case _                       =>
      sys.error("usage: sbt \"frflowNextInit NAME [--as DECIDER]\"  (a lowercase name: the project and package)")

  private def made(name: String, as: Option[String], extensions: Option[String], next: String => List[String])
      : Unit =
    val base = Path.of(sys.props("user.dir"))
    val files = write(base, name, extensions).fold(why => sys.error(s"init: $why"), identity)
    val listed = as.map(who => ReportText.listed(FrFlowApi.firstDecider[IO](base.resolve(s"examples/$name"), who,
      sys.env).unsafeRunSync()))
    println(((s"created the project $name:" :: files.map("  " + _)) ++ listed.toList ++ ("" :: next(name)))
      .mkString("\n"))

  /** What a new project is made of, relative to the build's directory. */
  def files(name: String, extensions: Option[String]): List[(String, String)] = List(
    s"examples/$name/src/main/scala/$name/Model.scala" -> model(name, extensions.fold("")(e => s", extensions = $e")),
    s"examples/$name/src/test/scala/$name/${name.capitalize}Examples.scala" -> examples(name))

  private def model(name: String, layers: String): String =
    s"""package $name
         |
         |import frflow.*
         |
         |/** ${name.capitalize}: its root statements come next, each decided by the developer. */
         |val frModel = KnowledgeBase("${name.capitalize}")()
         |
         |object ${name}Cli extends frflow.cli.FrFlowApp(frModel, root = "examples/$name"$layers)
         |""".stripMargin

  private def examples(name: String): String =
    s"""package $name
         |
         |import frflow.*
         |
         |/** The FrModel's examples, ordinary tests (`sbt $name/test`), checked against the claims and the code. */
         |class ${name.capitalize}Examples extends FrFlowExamples(frModel)
         |""".stripMargin

  /** The project's line in build.sbt: the examples' test framework and the Test dependency it runs from; no layer on
    * top on its classpath, unless it uses one.
    */
  def buildLine(name: String, layered: Boolean): String =
    val layers = if layered then "" else ", layers = Nil"
    s"""lazy val $name = nextExample("$name"$layers).dependsOn(nextTesting % Test)
       |  .settings(testFrameworks += TestFramework("frflow.testing.examples.ExamplesFramework"))""".stripMargin

  /** Writes the project under `base` (the build's directory), or says why not; nothing is written if any check
    * fails.
    */
  def write(base: Path, name: String, extensions: Option[String]): Either[String, List[String]] =
    val build = base.resolve("build.sbt")
    if !Name.matches(name) then Left(s"$name is not a lowercase name (letters and digits, starting with a letter)")
    else if !Files.isRegularFile(build) then Left(s"no build.sbt in $base: run it from the build's directory")
    else if Files.exists(base.resolve(s"examples/$name")) then Left(s"examples/$name exists already")
    else if Files.readString(build, UTF_8).linesIterator.exists(_.startsWith(s"lazy val $name ")) then
      Left(s"build.sbt has a project $name already")
    else
      val written = files(name, extensions).map { (rel, text) =>
        val p = base.resolve(rel)
        val _ = Files.createDirectories(p.getParent)
        val _ = Files.writeString(p, text, UTF_8)
        rel
      }
      val line = s"\n${buildLine(name, extensions.isDefined)}\n"
      val _ = Files.writeString(build, line, UTF_8, StandardOpenOption.APPEND)
      Right(written :+ "build.sbt (its project line)")
