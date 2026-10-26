package frflow.dsl.kb

import frflow.core.spec.Statement
import frflow.dsl.node.Node

/** `kb.implement(c, calls*)(code)`, `kb.implementProven(c)(define)`: inline only to take the code's text and the files
  * it refers to, then `attach`.
  */
object Implementing:
  extension (kb: KnowledgeBase)
    def implement[F](promise: Node[Statement.Contract | Statement.AssumedCall, F]): KnowledgeBase = ???
    def implementProven[F](contract: Node[Statement.Contract | Statement.FlowContract, F]): KnowledgeBase = ???
