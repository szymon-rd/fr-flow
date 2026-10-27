package frflow.agent

import frflow.api.Front
import scala.util.matching.Regex

/** The agent layer is a front end: it sees the API's views and algebras, the CLI and the web view, never the shell.
  * No source of it names `frflow.project`, `frflow.proof`, `frflow.testing` or `frflow.wire`, nor the API's own
  * `derive` and `shell`, and no class compiled from it refers to them. Nor does it decide: it reads (`Host.reading`),
  * and nothing of it calls a decision, previews one, rebases, lists a decider, or makes a decision for the command
  * line to run.
  */
class ArchitectureSuite extends munit.FunSuite:
  private val root = "next/agent/src/main/scala/frflow/agent"

  test("no source of the agent layer names project, proof, testing, wire, or the API's derive and shell") {
    assertEquals(Front.named(root), Nil)
  }

  test("no class compiled from the agent layer refers to them") {
    assertEquals(Front.compiled(Agent.getClass), Nil)
  }

  test("nothing of the agent layer decides, previews a decision, rebases or lists a decider") {
    val decides = """deciding\s*\.|firstDecider|\.\s*(decide|preview|rebase)\s*\(|Command\s*\.\s*""" +
      """(Decision|Rebase|Deciders)\b|\bDeciding\b|\bFrFlowApi\b|rules\s*\.\s*(Command|\{[^}]*\bCommand\b)"""
    assertEquals(Front.named(root, Regex(decides)), Nil)
    assertEquals(Front.compiled(Agent.getClass, Regex("frflow/api/(Deciding|FrFlowApi)\\b|frflow/decision/rules/" +
      "Command\\b|" +
      "frflow/cli/command/(Command\\$(Decision|Rebase|Deciders)|DecisionCommands|Dispatch)\\b")), Nil)
  }
