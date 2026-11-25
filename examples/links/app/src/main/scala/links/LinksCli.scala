package links

/** The link shortener's command line (`bin/frflow links COMMAND`, `sbt "links/serve --as NAME"`), over the model in
  * examples/links, with no layer on top.
  */
object linksCli extends frflow.cli.FrFlowApp(links, root = "examples/links")
