package fullshortener

/** The full shortener's command line (`bin/frflow fullshortener COMMAND`), over the model in
  * examples/fullshortener, with no layer on top.
  */
object fullshortenerCli extends frflow.cli.FrFlowApp(fullShortener, root = "examples/fullshortener")
