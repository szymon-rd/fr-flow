package frflow.agent

import frflow.cli.Front

/** The agent layer is a front end: it sees the API's views and algebras, the CLI and the web view, never the shell.
  * No source of it names `frflow.project`, `frflow.proof`, `frflow.testing` or `frflow.wire`, nor the API's own
  * `derive` and `shell`.
  */
class ArchitectureSuite extends munit.FunSuite:
  test("no source of the agent layer names project, proof, testing, wire, or the API's derive and shell") {
    assertEquals(Front.named("next/agent/src/main/scala/frflow/agent"), Nil)
  }
