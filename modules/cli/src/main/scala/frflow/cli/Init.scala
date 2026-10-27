package frflow
package cli

import java.nio.file.{Files, Path, StandardOpenOption}

/** A new project in this build: `sbt "frflowInit toy"`. It writes an empty FrModel and its main object, and the
  * project's line in build.sbt (`render` makes `lean/`). What comes next is IDEA.md: what the system is for, in prose,
  * which the developer accepts before the root. A layer on top (`frflow.agent.Init`) makes the same project with its
  * extensions in the main object.
  */
object Init:
  private val Name = "[a-z][a-z0-9]*".r

  // A plain main: it runs inside sbt (`cli/runMain`), where an effect runtime would warn about sbt's threads.
  def main(args: Array[String]): Unit = run(args.toList, None, name => List(
    s"next: sbt reload; write examples/$name/IDEA.md (what the system is for), accept it, then propose the root:",
    s"  bin/frflow $name status"))

  /** Writes the project named in `args`, with `extensions` (Scala, as the main object passes them); prints `next`. */
  def run(args: List[String], extensions: Option[String], next: String => List[String]): Unit = args match
    case List(name) =>
      write(Path.of(sys.props("user.dir")), name, extensions) match
        case Right(files) => println(((s"created the project $name:" :: files.map("  " + _)) ++ ("" :: next(name))).mkString("\n"))
        case Left(why) => sys.error(s"frflowInit: $why")
    case _ => sys.error("usage: sbt \"frflowInit NAME\"  (a lowercase name: the sbt project and the package)")

  /** What a new project is made of, relative to the build's directory. */
  def files(name: String, extensions: Option[String] = None): List[(String, String)] =
    val kb = name.capitalize
    val layers = extensions.fold("")(e => s", extensions = $e")
    List(
      s"examples/$name/src/main/scala/$name/Knowledge.scala" ->
        s"""package $name
           |
           |import frflow.*
           |
           |/** $kb: empty until the developer accepts IDEA.md; the root comes next. */
           |val knowledge = FrModel("$kb", idea = "IDEA.md")()
           |
           |object ${name}Cli extends frflow.cli.FrFlowApp(knowledge, root = "examples/$name"$layers)
           |""".stripMargin)

  /** The project's line in build.sbt: with no layer on top on its classpath, unless it uses one. */
  def buildLine(name: String, layered: Boolean = false): String =
    if layered then s"""lazy val $name = example("$name")""" else s"""lazy val $name = example("$name", layers = Nil)"""

  /** Writes the project under `base` (the build's directory), or says why not; nothing is written if any check fails. */
  def write(base: Path, name: String, extensions: Option[String] = None): Either[String, List[String]] =
    val build = base.resolve("build.sbt")
    val dir = base.resolve(s"examples/$name")
    if !Name.matches(name) then Left(s"$name is not a lowercase name (letters and digits, starting with a letter)")
    else if !Files.isRegularFile(build) then Left(s"no build.sbt in $base: run it from the build's directory")
    else if Files.exists(dir) then Left(s"examples/$name exists already")
    else if Files.readString(build).linesIterator.exists(_.startsWith(s"lazy val $name ")) then Left(s"build.sbt has a project $name already")
    else
      val written = files(name, extensions).map { (rel, text) =>
        val p = base.resolve(rel)
        Files.createDirectories(p.getParent)
        Files.writeString(p, text)
        rel
      }
      Files.writeString(build, s"\n${buildLine(name, extensions.isDefined)}\n", StandardOpenOption.APPEND)
      Right(written :+ "build.sbt (its project line)")
