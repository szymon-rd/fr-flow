package ox

/** The command line of the model of Ox's threads (`bin/frflow ox COMMAND`), over the model in examples/ox. Named
  * as the project is.
  */
object oxCli extends frflow.cli.FrFlowApp(ox.threads.oxThreads, root = "examples/ox")
