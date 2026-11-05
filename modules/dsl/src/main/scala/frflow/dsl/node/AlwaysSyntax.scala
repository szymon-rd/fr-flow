package frflow.dsl.node

import frflow.core.term.World
import frflow.dsl.build.Source
import frflow.dsl.model.StateModel
import frflow.dsl.shape.Defines
import frflow.dsl.vocab.Definition
import frflow.dsl.build.Fault
import frflow.dsl.term.{LeanType, Notes, Term, Terms}

/** The two `always`s, beside `forall` (every possible value): `always[T](x => …)`, every value of `T` that can be
  * made; `always(stored)(s => …)`, every state a model's state reaches. The rule is a define named as the node's
  * val, so Lean names it in every hypothesis it becomes.
  */
object AlwaysSyntax:
  inline def always[A: LeanType](inline rule: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.always[A](Source.of(rule).params.headOption.getOrElse("x"), applied(Defines.define(rule)))

  inline def always[S](model: StateModel[S])(inline rule: Term[S] => Term[Boolean]): Term[Boolean] =
    reached(model, Defines.define[S, Boolean](rule)(using model.stateType, LeanType[Boolean]))

  /** Every world reached, of two models' states in each: a rule relating them (the clock and a store, owner §47). */
  inline def always[S, U](a: StateModel[S], b: StateModel[U])(inline rule: (Term[S], Term[U]) => Term[Boolean])
      : Term[Boolean] =
    reachedBy(Defines.define[S, U, Boolean](rule)(using a.stateType, b.stateType, LeanType[Boolean]))(
      (r, w) => r(a.in(w), b.in(w))(using a.stateType, b.stateType, LeanType[Boolean]))

  /** Every world reached, of three models' states in each. */
  inline def always[S, U, V](a: StateModel[S], b: StateModel[U], c: StateModel[V])(
      inline rule: (Term[S], Term[U], Term[V]) => Term[Boolean]): Term[Boolean] =
    reachedBy(Defines.define[S, U, V, Boolean](rule)(using a.stateType, b.stateType, c.stateType,
      LeanType[Boolean]))((r, w) =>
      r(a.in(w), b.in(w), c.in(w))(using a.stateType, b.stateType, c.stateType, LeanType[Boolean]))

  /** The rule as the function `Terms.always` binds: its define applied to the bound value. A rule reading state is
    * refused: it holds of every value, in every world, of the value alone (owner §43).
    */
  def applied[A](rule: Definition[A => Boolean]): Term[A] => Term[Boolean] = x =>
    if rule.readsWorld then Term.noted(Notes.fault(Fault.WorldRead(s"the rule ${rule.name.value}")))(rule(x).run)
    else rule(x)

  /** Every world reached: its rule of the model's state in each. A rule reading state otherwise is refused, as a
    * value rule is (`applied`).
    */
  def reached[S](model: StateModel[S], rule: Definition[S => Boolean]): Term[Boolean] =
    reachedBy(rule)((r, w) => r(model.in(w)))

  /** Every world reached: `rule` of the models' states in each, as `at` applies it. */
  def reachedBy[F](rule: Definition[F])(at: (Definition[F], Term[World]) => Term[Boolean]): Term[Boolean] =
    Terms.always[World]("w", w =>
      if rule.readsWorld then Term.noted(Notes.fault(Fault.WorldRead(s"the rule ${rule.name.value}")))(
        at(rule, w).run)
      else at(rule, w))
