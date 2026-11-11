package shop

/** The shop's command line (`bin/frflow shop COMMAND`), over the model in examples/shop. */
object shopCli extends frflow.cli.FrFlowApp(shop, root = "examples/shop")
