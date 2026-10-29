package frflow.dsl.model

import frflow.core.name.SymbolName
import frflow.core.term.Program
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.build.Declarations
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition

/** FrFlow's own clock (owner §36): two Definitions, the time now in seconds and a wait, and their model, a count of
  * seconds only sleeps move (`clockModel`). `Flow.timeout` and `Flow.retry` take them. A program calling either
  * declares the model, so Lean has its field of the World; its plain Scala is given as any model's
  * (`implementTested(now, sleep)(…)`). Written without the DSL's macros, which do not expand in the module defining
  * them.
  */
object Clock:
  private val seconds = Ty.Num(NumKind.Big)

  val now: Definition[Program[BigInt]] =
    new Definition[Program[BigInt]](SymbolName("now"), "the time now, in seconds", None)(using
      declaring[Program[BigInt]](Ty.FlowOf(seconds, None)))

  val sleep: Definition[BigInt => Program[Unit]] =
    new Definition[BigInt => Program[Unit]](SymbolName("sleep"), "a wait of the seconds given", None)(using
      declaring[BigInt => Program[Unit]](Ty.FnOf(List(seconds), Ty.FlowOf(Ty.Unit, None))))

  object clockModel extends StateModel[BigInt]("the time now, in seconds")(using StateModel.Named("clockModel"),
      LeanType[BigInt]):
    meant(now, Nil, Nil)(_ => state.get)
    meant(sleep, List(LeanType[BigInt]), List("seconds"))(xs =>
      state.update(t => t + Term.free[BigInt](xs(0))))

  /** The clock's Definitions' type, declaring the clock's model wherever one is mentioned. */
  private def declaring[A](t: Ty): LeanType[A] = new LeanType[A]:
    val ty: Ty = t
    lazy val declares: Declarations = clockModel.itself
