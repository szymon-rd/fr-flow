package crm

/** Crm's command line (`bin/frflow crm COMMAND`, `sbt "crm/serve --as NAME"`), over the model in examples/crm, with
  * the AI agent's layer.
  */
object crmCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/crm", extensions = List(frflow.agent.Agent))
