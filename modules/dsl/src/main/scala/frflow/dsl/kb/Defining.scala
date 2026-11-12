package frflow.dsl.kb

import frflow.core.code.{Attachment, Code, Values}
import frflow.core.name.RelPath
import frflow.dsl.build.{Deferred, Site, Source}
import frflow.dsl.lifted.steps.StructureCode
import frflow.dsl.node.Spans
import frflow.dsl.structure.StructureDeclaration
import frflow.dsl.shape.Defines
import frflow.dsl.term.Reify
import frflow.dsl.vocab.{Declaration, Definition}
import scala.annotation.publicInBinary

/** A Declaration given its meaning (`granted.define { … }`): the declaration's word, and what a FrModel that lists
  * it beside its nodes takes the word to mean (`gives`).
  */
final class Defined[A] @publicInBinary private[kb] (val of: Declaration[A], private[kb] val gives: FrModel)
    extends Definition[A](of.name, of.described, None, of.word.at)(using of.leanType)

/** How a Declaration is given its meaning (owner §15), each a Definition of it, listed in the FrModel beside the
  * nodes and checked against every claim mentioning the Declaration: `define` (a define, lifted code, a class read
  * for a structure; the prover proves it, `impl`), `defineTested` (plain Scala, tested on generated cases),
  * `defineValue` (a value fixed in the model), `provided` (a value provided where the code runs).
  */
object Defining:
  extension [A](d: Declaration[A])
    /** `d` is `code`, which Lean proves meets each claim mentioning `d`; the files `code` is written in are the
      * model's own.
      */
    inline def define(code: Definition[A]): Definition[A] = Defining.proven(d, code, Spans.relative(Source.file))

    /** `granted.define { (held, request) => … }`: `d` is the define written here, named as its val. */
    inline def define(inline body: Defines.Lam[A]): Definition[A] =
      Defining.proven(d, Defines.of[A](body), Spans.relative(Source.file))

    /** `d` is plain Scala, built from the values it is given and calling other words
      * (`granted.defineTested(env => (held, request) => …)`), tested against each claim mentioning `d`.
      */
    inline def defineTested(inline code: Values => A): Definition[A] =
      Defined(d, Tested[A](FrModel.part, List(d.word))(code))

    /** The same, the plain Scala calling `calls` too, each a define the evaluator runs for it (`env(define)`). */
    inline def defineTestedCalling(calls: Declaration[?]*)(inline code: Values => A): Definition[A] =
      Defined(d, Tested[A](FrModel.part, d.word :: calls.toList.map(_.word))(code))

    /** `d` is `value`, fixed in the model. */
    inline def defineValue(value: A): Definition[A] =
      val at = Spans.relative(Source.file)
      Defined(d, Implementing.attach(FrModel.part, d.word, Reify(d.leanType, value).fold(
        Deferred.failed(Site.Meaning(d.name), _), v => Deferred.pure(Attachment(Code.Valued(v), at)))))

    /** The value of `d` is provided where the code runs: bound by an example, drawn by a test, passed in
      * production; Lean states every claim for each.
      */
    inline def provided: Definition[A] = Defined(d, Implementing.attach(FrModel.part, d.word,
      Deferred.pure(Attachment(Code.Provided, Spans.relative(Source.file)))))

  extension [T](d: StructureDeclaration[T])
    /** The structure `d` is the class read here (`limits.define(lifted[RecordedLimits])`): each member's code, which
      * Lean proves meets each claim mentioning the member.
      */
    inline def define[C <: T](code: StructureCode[C]): Definition[T] =
      Defined(d, Implementing.proven(FrModel.part, d, code, Spans.relative(Source.file)))
    /** The structure `d` is provided where the code runs (a library's, a remote service): no class is read for it.
      * It is known by what is assumed of it, and Lean states every claim of a structure that holds it for each
      * such structure.
      */
    inline def provided: Definition[T] =
      Defined(d, Implementing.provided(FrModel.part, d, Spans.relative(Source.file)))

  /** `d` given `code`, in the model file `at`. */
  def proven[A](d: Declaration[A], code: Definition[A], at: RelPath): Definition[A] =
    Defined(d, Implementing.proven(FrModel.part, d, code, at))
