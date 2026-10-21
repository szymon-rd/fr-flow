package frflow.examples.authz

import frflow.cli.FrFlowCli

/** `sbt "authz/run check"`, or `FRFLOW_ROOT=<dir>` to point at another workspace. */
@main def authz(args: String*): Unit =
  sys.exit(FrFlowCli.run(AuthzTheory, FrFlowCli.workspace("examples/authz", "../../../lean"), args))
