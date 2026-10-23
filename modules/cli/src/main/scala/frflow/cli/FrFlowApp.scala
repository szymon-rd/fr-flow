package frflow
package cli

/** The command line of a knowledge base, which a project's main object extends:
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth")
  * }}}
  * `root` is the project's directory (`FRFLOW_ROOT` overrides it); `kernelPath`, FrFlow's Lean kernel
  * relative to the project's `lean/`.
  */
abstract class FrFlowApp(knowledge: => KnowledgeBase, root: String = ".", kernelPath: String = "../../../lean"):
  final def main(args: Array[String]): Unit =
    sys.exit(Cli.run(knowledge, Cli.workspace(root, kernelPath), args.toSeq))
