package frflow.dsl.kb

import cats.MonadThrow
import frflow.core.code.{Attachment, Code, Impl, ScalaCode, Values}
import frflow.core.name.SourceText
import frflow.dsl.build.{Deferred, Source, SourceFiles}
import frflow.dsl.node.Spans
import frflow.dsl.vocab.Definition

/** `implementTested(ds*)` waiting for its Scala, typed by the Definitions (`TestedMacro`): `F` the first one's type,
  * `Ss` each one's shape as an operation on a state. One argument gives the first its plain Scala; two, `start` and
  * `observe`, begin the Scala of operations on one state.
  */
final class Tested[F, Ss <: Tuple](kb: FrModel, ds: List[Definition[?]]):
  /** The first Definition is plain Scala, built from the values it is given (`env(e)`), calling the others: tested
    * against each claim mentioning it. The files its Scala refers to are the code each such claim governs: a change to
    * one brings the claim back for review.
    */
  inline def apply(inline code: Values => F): FrModel =
    val d = ds.head
    val runs = ScalaCode(Impl(Implementing.arity(d.leanType.ty), env => code(env).asInstanceOf[AnyRef]),
      SourceText(Source.of(code).text), SourceFiles.of(code).map(Spans.relative))
    Implementing.attach(kb, d, Deferred.pure(Attachment(Code.Tested(runs, ds.tail.map(_.name)),
      Spans.relative(Source.file))))

  /** The Definitions are operations on one state, their meaning their model's: `start` makes their Scala hold a state
    * of the model, `observe` reads its state back; the next argument gives each operation's function (`Calls`). Each
    * is in the one effect `G`.
    */
  inline def apply[G[_], S, I](inline start: S => G[I], inline observe: I => G[S])(using g: MonadThrow[G])
      : Calls[G, I, Ss] =
    Calls(kb, ds, Calls.Ends((s: Any) => start(s.asInstanceOf[S]), (i: Any) => observe(i.asInstanceOf[I]),
      s"start = ${Source.of(start).text}, observe = ${Source.of(observe).text}",
      SourceFiles.of(start) ++ SourceFiles.of(observe)), g)
