package frflow.cli

import cats.effect.std.Console
import cats.effect.{ExitCode, IO, IOApp}
import cats.syntax.all.*
import frflow.api.FrFlowApi
import frflow.cli.text.ReportText
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardOpenOption}

/** A new project in this build: `sbt "frflowNextInit toy --as NAME"` (run forked from the build's directory). It
  * writes an empty FrModel and its main object, a class for its examples, and the project's line in build.sbt (its
  * examples run by `sbt toy/test`); with `--as`, the developer's own act, it lists the developer's key as the first
  * decider (`.frflow/deciders`, signed by it). A layer on top (`frflow.agent.Init`) makes the same project with its
  * extensions in the main object.
  */
object Init extends IOApp:
  private val Name = "[a-z][a-z0-9]*".r

  def run(args: List[String]): IO[ExitCode] = made(args, None, name => List(
    s"next: sbt reload; propose the root statements in examples/$name, then see where they stand:",
    s"  sbt \"$name/run status\""))

  /** Writes the project named in `args` (`NAME [--as DECIDER]`) in the build at the working directory, with
    * `extensions` (Scala, as the main object passes them), and prints `next`; a usage error, or why not, exits 2.
    */
  def made(args: List[String], extensions: Option[String], next: String => List[String]): IO[ExitCode] =
    args match
      case List(name)              => written(name, None, extensions).flatMap(said(name, next))
      case List(name, "--as", who) => written(name, Some(who), extensions).flatMap(said(name, next))
      case _                       => Console[IO].errorln("usage: sbt \"frflowNextInit NAME [--as DECIDER]\"  (a " +
          "lowercase name: the project and package)").as(ExitCode(2))

  /** The files written and, with a decider named, the deciders' list; or why not. */
  private def written(name: String, as: Option[String], extensions: Option[String])
      : IO[Either[String, List[String]]] =
    IO(Path.of(sys.props("user.dir"))).flatMap(base => write(base, name, extensions).flatMap(_.flatTraverse(files =>
      as.traverse(who => FrFlowApi.firstDecider[IO](base.resolve(s"examples/$name"), who, sys.env))
        .map(listed => Right(files ++ listed.map(ReportText.listed).toList)))))

  private def said(name: String, next: String => List[String])(r: Either[String, List[String]]): IO[ExitCode] =
    r.fold(why => Console[IO].errorln(s"init: $why").as(ExitCode(2)), lines =>
      IO.println(((s"created the project $name:" :: lines.map("  " + _)) ++ ("" :: next(name))).mkString("\n"))
        .as(ExitCode.Success))

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
         |val frModel = FrModel("${name.capitalize}")()
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
  def write(base: Path, name: String, extensions: Option[String]): IO[Either[String, List[String]]] = IO.blocking {
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
  }
