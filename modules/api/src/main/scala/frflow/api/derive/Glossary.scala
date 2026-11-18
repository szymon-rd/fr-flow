package frflow.api.derive

import frflow.api.view.vocab.*
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.DataType
import frflow.project.pipeline.Analysis
import frflow.proof.layout.Layout

/** The model's words (`Vocab`), from the analysis: each with what gives it its meaning (`Written.by`), each define
  * with its Rocq as `render` writes it.
  */
private[api] object Glossary:
  def of(a: Analysis): Vocab =
    val t = a.decided.theory
    val v = t.vocabulary
    val meant = (s: SymbolName) => t.code.attached.get(s).map(c => Written.by(t, c.code))
    Vocab(v.symbols.map(s => Word(s.name, s.means, s.kind, s.ty, meant(s.name))),
      v.defines.map(d => Defined(d.name, doc(a, d.name.value), d.written.source.value, rocq(a, d.name))),
      v.sorts.map(s => DomainType(s.name, Shape.Opaque(s.means))) ++ v.types.map(d => DomainType(d.typeName, shape(d))))

  /** A define's Scaladoc, from the files the model records it written in. */
  private def doc(a: Analysis, name: String): Option[String] =
    val files = a.decided.theory.own.vocabulary.toList.collect { case (f, names) if names(name) => f }
    DocComments.of(name, files, a.inputs.sources)

  private def rocq(a: Analysis, d: DefName): Option[String] =
    a.rocq.text(Layout(a.decided.theory.name).define(d))

  private def shape(d: DataType): Shape = d match
    case DataType.Product(_, _, fields) => Shape.Record(fields)
    case DataType.Sum(_, _, cases)      => Shape.Choice(cases.toList.map(c => Case(c.name.value, c.fields)))
