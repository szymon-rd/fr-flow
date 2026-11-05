package sharing

/** Sharing's command line (`bin/frflow sharing COMMAND`, `sbt "sharing/serve --as NAME"`), over the model in
  * examples/sharing, with the AI agent's layer.
  */
object sharingCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/sharing",
    extensions = List(frflow.agent.Agent))
