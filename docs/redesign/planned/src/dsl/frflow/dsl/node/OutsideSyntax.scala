package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.expr.OutsideFact
import frflow.core.name.DefName
import frflow.core.term.Sym
import frflow.dsl.build.Declarations
import frflow.dsl.flow.Boundary
import frflow.dsl.model.StoreModel
import frflow.dsl.shape.Defines
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.dsl.vocab.Definition

/** What the world outside the code is assumed to do (owner §16, §17), each a formula of `Node.assumption`: the
  * company's procedures, the outside services and how they are run. FrFlow's rules rest on them (`Premises`); Lean
  * states none of them as a formula. What values from outside meet is said with `always` on their type instead
  * (`Node.assumption("…")(always[Request](r => …))`, owner §21).
  */
object OutsideSyntax:
  extension [B[_[_], _[_]]](store: Boundary[B])
    /** The store does what its model does. */
    def behavesAs[S](model: StoreModel[B, S]): Term[Boolean] =
      fact(model.declares, OutsideFact.BehavesAs(store.name, model.name))

  extension [B[_[_], _[_]], S](model: StoreModel[B, S])
    /** What the state the store starts in meets (`stored.initially(held => held === Nil)`): the rule a define named
      * as the assumption's val.
      */
    inline def initially(inline rule: Term[S] => Term[Boolean]): Term[Boolean] =
      started(model, Defines.define(rule)(using model.state.leanType, LeanType[Boolean]))
    /** Only these programs change its state. */
    def writtenOnlyBy(programs: Definition[?]*): Term[Boolean] =
      fact(model.declares, OutsideFact.WrittenOnlyBy(model.name, programs.toList.map(_.name)))
    /** Runs changing its state never interleave: one process running each atomically, or a store serializing them. */
    def changedOneRunAtATime: Term[Boolean] = fact(model.declares, OutsideFact.OneRunAtATime(model.name))

  /** The start's rule as a fact, noting its define. */
  def started[B[_[_], _[_]], S](model: StoreModel[B, S], rule: Definition[S => Boolean]): Term[Boolean] =
    fact(model.declares |+| rule.notes.declares, OutsideFact.Initially(model.name, DefName(rule.name.value)))

  private def fact(declares: Declarations, f: OutsideFact): Term[Boolean] =
    Term.noted(Notes.of(declares))([T[_]] => (s: Sym[T]) => s.outside(f))
