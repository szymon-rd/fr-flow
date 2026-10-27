package frflow.web

import frflow.api.Front
import scala.util.matching.Regex

/** The web view is a front end: it sees the API's views and algebras (and the core, DSL, decision and eval values
  * they carry), never the shell. No source of it, outside its string literals and comments, names `frflow.project`,
  * `frflow.proof`, `frflow.testing` or `frflow.wire`, nor the API's own `derive` and `shell`; nor the command line,
  * which it does not depend on; and no class compiled from it refers to them.
  */
class ArchitectureSuite extends munit.FunSuite:
  test("no source of the web view names project, proof, testing, wire, the API's derive and shell, or the CLI") {
    val shell = Regex(Front.Shell.regex + """|frflow\s*\.\s*cli\b|frflow\s*\.\s*\{[^}]*\bcli\b""")
    assertEquals(Front.named("next/web/src/main/scala/frflow/web", shell), Nil)
  }

  test("no class compiled from the web view refers to them") {
    assertEquals(Front.compiled(WebView.getClass, Regex(Front.ShellClasses.regex + "|frflow/cli/")), Nil)
  }
