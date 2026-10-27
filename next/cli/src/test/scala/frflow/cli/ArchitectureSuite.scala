package frflow.cli

/** The command line is a front end: it sees the API's views and algebras (and the core, DSL, decision and eval values
  * they carry), never the shell. No source of it names `frflow.project`, `frflow.proof`, `frflow.testing` or
  * `frflow.wire`, though depending on the API puts them on its classpath; nor the API's own `derive` and `shell`.
  */
class ArchitectureSuite extends munit.FunSuite:
  test("no source of the command line names project, proof, testing, wire, or the API's derive and shell") {
    assertEquals(Front.named("next/cli/src/main/scala/frflow/cli"), Nil)
  }
