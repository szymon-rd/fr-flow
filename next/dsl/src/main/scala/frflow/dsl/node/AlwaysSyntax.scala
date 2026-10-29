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
    Terms.always[World]("w", w =>
      if rule.readsWorld then Term.noted(Notes.fault(Fault.WorldRead(s"the rule ${rule.name.value}")))(
        rule(model.in(w)).run)
      else rule(model.in(w)))
