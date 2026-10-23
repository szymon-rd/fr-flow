package frflow
package cli

import java.nio.file.{Files, Path, StandardOpenOption}

/** A new project in this build, before the developer has told the agent anything: `sbt "frflowInit toy"`. It writes
  * an empty knowledge base and its main object, and the project's line in build.sbt (`render` makes `lean/`). The idea comes
  * next, in chat: the agent records it (`said`, `asked`, `replied`) and writes IDEA.md from it.
  */
object Init:
  private val Name = "[a-z][a-z0-9]*".r

  // A plain main: it runs inside sbt (`cli/runMain`), where an effect runtime would warn about sbt's threads.
  def main(args: Array[String]): Unit = args.toList match
    case List(name) =>
      write(Path.of(sys.props("user.dir")), name) match
        case Right(files) =>
          println(((s"created the project $name:" :: files.map("  " + _)) ++ List("",
            "next: sbt reload; then tell the agent your idea in chat, and see where it stands:",
            s"  bin/frflow $name status")).mkString("\n"))
        case Left(why) => sys.error(s"frflowInit: $why")
    case _ => sys.error("usage: sbt \"frflowInit NAME\"  (a lowercase name: the sbt project and the package)")

  /** What a new project is made of, relative to the build's directory. */
  def files(name: String): List[(String, String)] =
    val kb = name.capitalize
    List(
      s"examples/$name/src/main/scala/$name/Knowledge.scala" ->
        s"""package $name
           |
           |import frflow.*
           |
           |/** $kb: empty until the developer accepts IDEA.md, which the agent writes from their conversation; the root
           |  * comes next.
           |  */
           |val knowledge = KnowledgeBase("$kb", idea = "IDEA.md")()
           |
           |object ${name}Cli extends frflow.cli.FrFlowApp(knowledge, root = "examples/$name")
           |""".stripMargin)

  /** The project's line in build.sbt. */
  def buildLine(name: String): String = s"""lazy val $name = example("$name")"""

  /** Writes the project under `base` (the build's directory), or says why not; nothing is written if any check fails. */
  def write(base: Path, name: String): Either[String, List[String]] =
    val build = base.resolve("build.sbt")
    val dir = base.resolve(s"examples/$name")
    if !Name.matches(name) then Left(s"$name is not a lowercase name (letters and digits, starting with a letter)")
    else if !Files.isRegularFile(build) then Left(s"no build.sbt in $base: run it from the build's directory")
    else if Files.exists(dir) then Left(s"examples/$name exists already")
    else if Files.readString(build).linesIterator.exists(_.startsWith(s"lazy val $name ")) then Left(s"build.sbt has a project $name already")
    else
      val written = files(name).map { (rel, text) =>
        val p = base.resolve(rel)
        Files.createDirectories(p.getParent)
        Files.writeString(p, text)
        rel
      }
      Files.writeString(build, s"\n${buildLine(name)}\n", StandardOpenOption.APPEND)
      Right(written :+ "build.sbt (its project line)")
