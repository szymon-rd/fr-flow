package payments

/** Payments's command line (`bin/frflow payments COMMAND`). */
object paymentsCli extends frflow.cli.FrFlowApp(Payments.model, root = "examples/payments", extensions = List(frflow.agent.Agent))
