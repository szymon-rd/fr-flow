package ox

/** The command line of the model of Ox's scopes (`bin/frflow ox COMMAND`), over the model in examples/ox. Named
  * as the project is; Ox itself is not on this classpath.
  */
object oxCli extends frflow.cli.FrFlowApp(scopes.scopes, root = "examples/ox")
