package wallet

/** The wallet's command line (`bin/frflow wallet COMMAND`), over the model in examples/wallet. */
object walletCli extends frflow.cli.FrFlowApp(wallet, root = "examples/wallet")
