package frflow.dsl.kb

import frflow.core.code.{Attachment, Code, CodeFile, Impl, ScalaCode, Values}
import frflow.core.name.SourceText
import frflow.dsl.build.{Deferred, Source, SourceFiles}
import frflow.dsl.node.Spans
import frflow.dsl.vocab.Definition

/** `d.defineTested(…)` waiting for its Scala: `F` the type of the first Definition, whose plain Scala is given; the
  * others are the defines it calls.
  */
final class Tested[F](kb: FrModel, ds: List[Definition[?]]):
  /** The first Definition is plain Scala, built from the values it is given (`env(e)`), calling the others: tested
    * against each claim mentioning it. The files its Scala refers to are the code each such claim governs: a change to
    * one brings the claim back for review.
    */
  inline def apply(inline code: Values => F): FrModel =
    val d = ds.head
    val runs = ScalaCode(Impl(Implementing.arity(d.rocqType.ty), env => code(env).asInstanceOf[AnyRef]),
      SourceText(Source.of(code).text), Tested.files(SourceFiles.of(code)))
    Implementing.attach(kb, d, Deferred.pure(Attachment(Code.Tested(runs, ds.tail.map(_.name)),
      Spans.relative(Source.file))))

object Tested:
  /** The files plain Scala refers to, each relative to the project, with what it refers to in each. */
  def files(found: List[(String, List[String])]): List[CodeFile] =
    CodeFile.merged(found.map((f, ns) => CodeFile(Spans.relative(f), ns)))
