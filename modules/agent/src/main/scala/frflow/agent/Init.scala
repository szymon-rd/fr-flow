package frflow.agent

/** A new project with the agent's layer: `sbt "frflowInitAgent toy"`. The idea comes next, in chat: the agent records it
  * (`said`, `asked`, `replied`) and writes IDEA.md from it.
  */
object Init:
  def main(args: Array[String]): Unit = frflow.cli.Init.run(args.toList, Some("List(frflow.agent.Agent)"), name => List(
    "next: sbt reload; then tell the agent your idea in chat, and see where it stands:", s"  bin/frflow $name status"))
