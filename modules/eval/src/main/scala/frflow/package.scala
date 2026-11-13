package frflow

/** The one facade a model imports (`import frflow.*`): the DSL, examples and their generators (`Gen`), and plain
  * code's syntax (`env(d)`, `d.fn(env)`, `knowledge.code(d)(…)`).
  *
  * Its names are an import's: a model's own top-level `val` or `def` of the same name, in scope where one is used,
  * hides it, and the use does not compile (`val after = …` hides `book(request).after`). The names it takes,
  * besides its types (`Gen` among them: a model's own of that name hides it): the extensions `refines`, `assuming`,
  * `replaces`, `result`, `after`, and `always`, `forall`, `exists`, `define`, `stated`, `lifted`, `holding`,
  * `contractOf`, `when`, `make`, `let`. An `Int` literal is a `Term[BigInt]` where one is expected (`given int`).
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
    * developer's, its members over domain types), `val limits = Declaration[CardLimits]("…")`, typed by the trait's
    * members.
    */
  transparent inline def apply[A](inline means: String): Declaration[A] = frflow.dsl.structure.Declaring[A](means)
export frflow.dsl.vocab.DefinitionSyntax.*
export frflow.dsl.kb.Gens
export frflow.core.example.Gen
export frflow.dsl.shape.Defines.*
export frflow.dsl.lifted.{Contract, FrSpec, Lifted}
export frflow.dsl.lifted.LiftSyntax.*
export frflow.dsl.compiled.steps.ClassSyntax.*
export frflow.dsl.structure.{Call, StructureDeclaration}
/** What a state of the structure whose trait is named `N` is typed by (`Term[StateOf[N]]`): for what a model says
  * of any structure's state (`def applied[H <: String](id: Term[PaymentId], in: Term[StateOf[H]])`).
  */
type StateOf[N <: String] = frflow.dsl.structure.State[N]
export frflow.dsl.term.TermSyntax.*
export frflow.dsl.kb.ValuesSyntax.*
export frflow.eval.term.DefSyntax.*
export frflow.eval.run.CodeSyntax.*
