package frflow.api

/** A layer on top of FrFlow, such as an AI agent's tools: a project's main object lists the ones it uses, and each front
  * end takes the parts it knows (the CLI's `CliExtension`, the web view's `WebExtension`). FrFlow itself needs none.
  */
trait Extension
