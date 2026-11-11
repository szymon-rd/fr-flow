package payments

/** The payment stream's command line (`bin/frflow payments COMMAND`), over the model in examples/payments. */
object paymentsCli extends frflow.cli.FrFlowApp(payments, root = "examples/payments")
