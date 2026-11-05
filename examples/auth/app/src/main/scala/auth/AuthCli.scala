package auth

/** Auth's command line (`bin/frflow auth COMMAND`, `sbt "auth/serve --as NAME"`), over the model in examples/auth,
  * with the AI agent's layer.
  */
object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth", extensions = List(frflow.agent.Agent))
