package frflow.cli

import frflow.api.Front

/** The command line is a front end: it sees the API's views and algebras (and the core, DSL, decision and eval values
  * they carry), never the shell. No source of it names `frflow.project`, `frflow.proof`, `frflow.testing` or
  * `frflow.wire`, though depending on the API puts them on its classpath; nor the API's own `derive` and `shell`;
  * and no class compiled from it refers to them, however a source spelled it.
  */
class ArchitectureSuite extends munit.FunSuite:
  test("no source of the command line names project, proof, testing, wire, or the API's derive and shell") {
    assertEquals(Front.named("next/cli/src/main/scala/frflow/cli"), Nil)
  }

  test("no class compiled from the command line refers to them") {
    assertEquals(Front.compiled(Launch.getClass), Nil)
  }

  test("the sources' scan sees an import in braces, a wildcard, and spaces; not a string or a comment") {
    val spelled = List("import frflow.{project as p}", "import frflow.api.{Reading, shell}", "import frflow.*",
      "import frflow . proof . lean", "frflow.wire.file.Files")
    val quiet = List("\"frflow.project\"", "// frflow.project", "/* frflow.wire */", "import frflow.api.Reading")
    assertEquals(spelled.map(Front.Shell.findFirstIn(_).isDefined), spelled.map(_ => true))
    assertEquals(quiet.map(s => Front.Shell.findFirstIn(Front.code(s)).isDefined), quiet.map(_ => false))
  }
