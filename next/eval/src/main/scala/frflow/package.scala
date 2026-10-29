package frflow

/** The one facade a model imports (`import frflow.*`): the DSL, programs, models of a state, examples, and plain
  * code's syntax (`env(d)`, `d.fn(env)`, `knowledge.code(d)(…)`, `knowledge.running[F](…)`).
  *
  * Its names are an import's: a model's own top-level `val` or `def` of the same name, in scope where one is used,
  * hides it, and the use does not compile (`val from = …` hides `book(request).from(now)`). The names it takes,
  * besides its types: the extensions `refines`, `assuming`, `replaces`, `from`, and `always`, `forall`, `define`,
  * `program`, `when`, `make`, `let`. An `Int` literal is a `Term[BigInt]` where one is expected (`given int`), and an
  * operation applied a step where a program expects one (`given step`).
  */
export frflow.dsl.node.Node
export frflow.dsl.node.NodeSyntax.*
export frflow.dsl.node.AlwaysSyntax.*
export frflow.dsl.kb.FrModel
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
export frflow.dsl.flow.{Flow, Recorded}
export frflow.dsl.model.{Clock, Fact, Model, StateModel}
export frflow.dsl.flow.FlowSyntax.*
export frflow.eval.term.DefSyntax.*
export frflow.eval.CodeSyntax.*
