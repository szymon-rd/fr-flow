package frflow.agent

/** A new project with the agent's layer: `sbt "frflowNextInitAgent toy --as NAME"` (`--as` lists the developer's key as
  * the first decider: the developer runs it, never the agent). The idea comes next, in chat: the agent records it
  * (`said`, `asked`, `replied`) and proposes the root statements from it.
  */
object Init:
  def main(args: Array[String]): Unit = frflow.cli.Init.run(args.toList, Some("List(frflow.agent.Agent)"), name =>
    List("next: sbt reload; then tell the agent your idea in chat, and see where it stands:",
      s"  sbt \"$name/run status\""))
