package frflow

/** The facade the examples import (`import frflow.*`), the DSL's part of it: `next-eval` gives the whole facade in
  * its main code (step 4), adding plain code's syntax (`d.fn(env)`, `knowledge.code(d)(…)`); this one then goes.
  */
export frflow.dsl.node.Node
export frflow.dsl.node.NodeSyntax.*
export frflow.dsl.node.AlwaysSyntax.*
export frflow.dsl.node.OutsideSyntax.*
export frflow.dsl.kb.KnowledgeBase
export frflow.dsl.kb.Implementing.*
export frflow.dsl.example.FrFlowExamples
export frflow.dsl.example.ExampleSyntax.*
export frflow.dsl.term.{Data, LeanType, Term}
export frflow.dsl.vocab.{Declaration, Definition, Opaque}
export frflow.dsl.vocab.DefinitionSyntax.*
export frflow.core.term.{Program, World}
export frflow.dsl.kb.Gens
export frflow.dsl.shape.Defines.*
export frflow.dsl.term.TermSyntax.*
export frflow.dsl.kb.ValuesSyntax.*
export frflow.dsl.flow.{Boundary, BoundaryOps, Clock, Flow}
export frflow.dsl.model.{Model, ModelState}
export frflow.dsl.model.ModelSyntax.*
export frflow.dsl.flow.FlowSyntax.*
