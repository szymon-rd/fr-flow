package frflow.dsl.kb

import cats.syntax.all.*
import frflow.core.code.{Attachment, Code, Impl, ScalaCode, Values}
import frflow.core.name.SourceText
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Deferred, Fault, Site, Source, SourceFiles}
import frflow.dsl.node.Spans
import frflow.dsl.term.Reify
import frflow.dsl.vocab.Definition

/** What gives each Definition its meaning (owner §15), one pattern, written once in the FrModel and checked
  * against every claim mentioning the Definition: `implementProven` (a define or a program; Lean proves it, `impl`),
  * `implementTested` (plain Scala, tested on generated cases), `implementValue` (a value fixed in the model),
  * `implementProvided` (a value provided where the code runs). Only a Definition takes any of them, and only one
  * that has no meaning where it is written: a Declaration has no meaning to give.
  */
object Implementing:
  extension (kb: FrModel)
    /** `d` is `proven` (a `define` or a `program`), which Lean proves meets each claim mentioning `d` (`impl`). */
    inline def implementProven[F](d: Definition[F])(proven: Definition[F]): FrModel =
      val at = Spans.relative(Source.file)
      Implementing.attach(kb, d, proven.onTheSpot.fold(Deferred.failed(Site.Meaning(d.name),
        Fault.NotProvenCode(proven.name.value)))(spot =>
          Deferred((Declarations.define(spot.name, spot.lambda), Attachment(spot.code, at)).validNec)))

    /** `d` is plain Scala, built from the values it is given (`env(e)`), calling the Definitions `calls`: tested
      * against each claim mentioning `d`. The files its Scala refers to are the code each such claim governs: a
      * change to one brings the claim back for review.
      */
    inline def implementTested[F <: AnyRef](d: Definition[F], calls: Definition[?]*)(inline code: Values => F)
        : FrModel =
      val runs = ScalaCode(Impl(Implementing.arity(d.leanType.ty), env => code(env)),
        SourceText(Source.of(code).text), SourceFiles.of(code).map(Spans.relative))
      Implementing.attach(kb, d, Deferred.pure(Attachment(Code.Tested(runs, calls.toList.map(_.name)),
        Spans.relative(Source.file))))

    /** `d` is `value`, fixed in the model. */
    inline def implementValue[A](d: Definition[A])(value: A): FrModel =
      val at = Spans.relative(Source.file)
      Implementing.attach(kb, d, Reify(d.leanType, value).fold(Deferred.failed(Site.Meaning(d.name), _),
        v => Deferred.pure(Attachment(Code.Valued(v), at))))

    /** The values of `ds` are provided where the code runs: bound by an example, drawn by a test, passed in
      * production; Lean states every claim for each.
      */
    inline def implementProvided(ds: Definition[?]*): FrModel =
      ds.foldLeft(kb)((k, d) =>
        Implementing.attach(k, d, Deferred.pure(Attachment(Code.Provided, Spans.relative(Source.file)))))

  /** The meaning given `d`, unless `d` has its own where it is written; a code-only `d` declared with it. */
  def attach(kb: FrModel, d: Definition[?], a: Deferred[Attachment]): FrModel =
    kb.attach(d.name, d.onTheSpot.fold(a.andThen(x => Deferred((d.declares, x).validNec)))(_ =>
      Deferred.failed(Site.Meaning(d.name), Fault.MeantWhereWritten(d.name.value))))

  /** How many inputs plain code of this type takes. */
  def arity(ty: Ty): Int = ty match
    case Ty.FnOf(ins, _) => ins.size
    case _               => 0
