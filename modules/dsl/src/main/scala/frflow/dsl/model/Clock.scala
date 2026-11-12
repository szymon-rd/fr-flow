package frflow.dsl.model

import cats.syntax.all.*
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.Timed
import frflow.dsl.build.{Declarations, Fault, WrittenAt}
import frflow.dsl.vocab.Flow
import frflow.dsl.shape.Defines
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition

/** FrFlow's own clock, as Cats Effect models time (owner §36, §47): its model's state is the time now, in seconds,
  * which only moves on (a wait or a step of the world by less than nothing moves it by nothing). Steps of code take
  * no time of their own; `now` reads the time, `sleep` lets at least the seconds given pass, and `elapse` is the
  * world's own step, taken between runs and never by code (`TestControl.advance`). Lean also lets the world move the
  * time on at each of the clock's steps, and reads waits at once as taking the longest of them, not the sum
  * (`Waits`). `Flow.timeout` and `Flow.retry` take `now` and `sleep`. A program calling either declares the model,
  * so Lean has its field of the World; its plain Scala, a virtual clock where it is tested, is given as any model's
  * (`defineOperations(now, sleep, elapse)(…)`). Written without the DSL's macros, which do not expand in the module
  * defining them, but for `schedule`'s rule.
  */
object Clock:
  private val seconds = Ty.Num(NumKind.Big)

  val now: Definition[Flow[BigInt]] =
    new Definition[Flow[BigInt]](SymbolName("now"), "the time now, in seconds", None, WrittenAt.none)(using
      declaring[Flow[BigInt]](Ty.FlowOf(seconds, None)))

  val sleep: Definition[BigInt => Flow[Unit]] =
    new Definition[BigInt => Flow[Unit]](SymbolName("sleep"), "a wait of at least the seconds given", None,
      WrittenAt.none)(using
      declaring[BigInt => Flow[Unit]](Ty.FnOf(List(seconds), Ty.FlowOf(Ty.Unit, None))))

  val elapse: Definition[BigInt => Flow[Unit]] =
    new Definition[BigInt => Flow[Unit]](SymbolName("elapse"), "time passing between runs, by the seconds given: " +
      "the world's own step, never code's", None, WrittenAt.none)(using
      declaring[BigInt => Flow[Unit]](Ty.FnOf(List(seconds), Ty.FlowOf(Ty.Unit, None))))

  object clockModel extends StateModel[BigInt]("the time now, in seconds")(using StateModel.Named("clockModel", None),
      LeanType[BigInt]):
    meant(now, Nil, Nil)(_ => state.get.steps)
    meant(sleep, List(LeanType[BigInt]), List("seconds"))(xs => state.update(on(_, xs(0))).steps)
    meant(elapse, List(LeanType[BigInt]), List("seconds"))(xs => state.update(on(_, xs(0))).steps)

    override protected def timed: Option[Timed] = Some(Timed(now.name, sleep.name, elapse.name))

    /** Where the world moves the time (owner §47's schedule, a trusted fact about the world's steps): only to a time
      * `rule` allows, given `other`'s state then (`clockModel.schedule(lastRun)((now, ran) => now <= ran + 120)`:
      * housekeeping runs at least every two minutes). Each move the world makes is one (its steps between runs, the
      * time passing at the clock's steps in a run, the end of a wait); a move it does not allow is not taken. The rule
      * is a define named as the assumption's val, over plain values: it reads no world and no other Definition.
      */
    inline def schedule[O](other: StateModel[O])(inline rule: (Term[BigInt], Term[O]) => Term[Boolean]): Fact =
      scheduled(other, Defines.define(rule)(using LeanType[BigInt], other.stateType, LeanType[Boolean]))

    def scheduled[O](other: StateModel[O], rule: Definition[(BigInt, O) => Boolean]): Fact =
      val f = Fact(Term.noted(Notes.of(declares |+| other.declares |+| rule.notes.declares))([T[_]] =>
        (s: frflow.core.term.language.Sym[T]) => s.outside(OutsideFact.Schedule(name, List(other.name),
          DefName(rule.name.value)))))
      if rule.readsWorld then Fact(Term.noted(Notes.fault(Fault.WorldRead(s"$name's schedule")))(f.term.run)) else f

  /** The time moved on by the seconds given, or kept where they are less than none. */
  private def on(t: Term[BigInt], by: frflow.core.expr.Binder): Term[BigInt] =
    val d = Term.free[BigInt](by)
    when(d >= 0)(t + d).otherwise(t)

  /** The clock's Definitions' type, declaring the clock's model wherever one is mentioned. */
  private def declaring[A](t: Ty): LeanType[A] = new LeanType[A]:
    val ty: Ty = t
    lazy val declares: Declarations = clockModel.itself
