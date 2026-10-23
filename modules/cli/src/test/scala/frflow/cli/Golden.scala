package frflow.cli

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** Output compared with a file in `src/test/resources/golden`; `FRFLOW_GOLDEN=update` (or the system property
  * `frflow.golden=update`, for an sbt server: `sbt "eval sys.props(\"frflow.golden\") = \"update\""`) writes the files instead.
  */
trait Golden:
  self: munit.FunSuite =>

  private def file(name: String) = Path.of(sys.props("user.dir"), "modules/cli/src/test/resources/golden", s"$name.txt")

  def golden(name: String, lines: Seq[String])(using munit.Location): Unit =
    val actual = lines.map(_.stripTrailing).mkString("", "\n", "\n")
    if sys.env.get("FRFLOW_GOLDEN").orElse(sys.props.get("frflow.golden")).contains("update") then
      Files.createDirectories(file(name).getParent)
      Files.writeString(file(name), actual, UTF_8)
    else
      val expected = Option(getClass.getResourceAsStream(s"/golden/$name.txt")).map(s => String(s.readAllBytes(), UTF_8))
      assertNoDiff(actual, expected.getOrElse(fail(s"no golden/$name.txt: run the tests with FRFLOW_GOLDEN=update, and read it")))
