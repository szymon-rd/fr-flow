package frflow

/** The one facade a model imports (`import frflow.*`): the DSL, the plain-code syntax (`d.fn`), and the run time's
  * syntax on a knowledge base (`knowledge.service(c)(…)`, `knowledge.run[IO](job)(…)`).
  */
export frflow.dsl.node.{Binding, Case, Node}
export frflow.dsl.node.NodeSyntax.*
export frflow.dsl.kb.KnowledgeBase
export frflow.dsl.kb.Implementing.*
export frflow.dsl.term.{Data, Def, Gens, LeanType, Opaque, Param, Term}
export frflow.dsl.term.TermSyntax.*
export frflow.dsl.term.Lift.given
export frflow.dsl.flow.{Boundary, Flow}
export frflow.eval.DefSyntax.*
export frflow.runtime.RunSyntax.*
