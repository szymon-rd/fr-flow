package frflow

/** The one facade a model imports (`import frflow.*`): the DSL, programs (`Flow`), models of a state, examples and
  * their generators (`Gen`), the plain Scala a model's tests give FrFlow's clock (`Wall`), and plain code's syntax
  * (`env(d)`, `d.fn(env)`, `knowledge.code(d)(…)`, `knowledge.running[F](…)`). The World is not among its names
  * (owner §41): a statement holds in every reachable world and reads what changes with it in the current one
  * (`storedBookings.current`, `book(request).result`, `storedBookings.in(book(request).after)`).
  *
  * Its names are an import's: a model's own top-level `val` or `def` of the same name, in scope where one is used,
  * hides it, and the use does not compile (`val after = …` hides `book(request).after`). The names it takes,
  * besides its types (`Gen` and `Wall` among them: a model's own of either name hides it): the extensions `refines`,
  * `assuming`, `replaces`, `result`, `after`, `failing`, `ifSucceeds`, `ifFails`, and `always`, `forall`, `exists`,
  * `define`, `stated`, `program`, `lifted`, `updating`, `interleaving`, `holding`, `contractOf`, `when`, `make`,
  * `let`. An `Int` literal is a `Term[BigInt]` where one is expected (`given int`), and an operation applied a
  * step where a program expects one (`Flow`'s `given asStep`).
  */
export frflow.dsl.node.Node
export frflow.dsl.node.NodeSyntax.*
export frflow.dsl.node.AlwaysSyntax.*
export frflow.dsl.kb.FrModel
export frflow.dsl.kb.Defining.*
export frflow.dsl.example.FrFlowExamples
export frflow.dsl.example.ExampleSyntax.*
export frflow.dsl.term.{Data, LeanType, Term}
export frflow.dsl.vocab.{Definition, Opaque, Stating}

/** A word of the model (`dsl.vocab.Declaration`): what statements speak of and code calls. A `Definition` is one
  * with a meaning.
  */
type Declaration[A] = frflow.dsl.vocab.Declaration[A]

object Declaration:
  /** `val granted = Declaration[(RoomBookings, Booking) => Boolean]("…")`; of a structure (a trait of the
    * developer's, its members over domain types), `val limits = Declaration[Limits]("…")`, typed by the trait's
    * members.
    */
  transparent inline def apply[A](inline means: String): Declaration[A] = frflow.dsl.structure.Declaring[A](means)
export frflow.dsl.vocab.DefinitionSyntax.*
export frflow.dsl.kb.Gens
export frflow.core.example.Gen
export frflow.dsl.shape.Defines.*
export frflow.dsl.lifted.{Contract, FrSpec, Lifted}
export frflow.dsl.lifted.LiftSyntax.*
export frflow.dsl.lifted.steps.StepSyntax.*
export frflow.dsl.structure.{Call, StructureDeclaration}
export frflow.dsl.term.TermSyntax.*
export frflow.dsl.kb.ValuesSyntax.*
export frflow.dsl.vocab.Flow
export frflow.dsl.model.{Clock, Fact, Model, StateModel}
export frflow.eval.flow.Wall
export frflow.dsl.vocab.FlowSyntax.*
export frflow.eval.term.DefSyntax.*
export frflow.eval.run.CodeSyntax.*
