package frflow.dsl.kb

import cats.data.ValidatedNec
import cats.syntax.all.*
import frflow.core.code.{Attachment, Code, CodeTable, Implementation}
import frflow.core.name.{ModelName, RelPath, SymbolName}
import frflow.core.vocab.Vocabulary
import frflow.dsl.build.{ElabError, Fault, Site}

/** The code table of an elaborated FrModel: what it gives each Definition, and each operation on a state its model
  * (`Code.Modelled`), with the Scala given each model's operations (`implementTested(ops*)`). Refused: an operation
  * two models give a meaning, or given another meaning beside its model's; Scala given operations no one model
  * gives a meaning, or given some of a model's operations only.
  */
object Modelled:
  def table(v: Vocabulary, attached: Map[SymbolName, Attachment], written: List[Operations], kb: Option[RelPath])
      : ValidatedNec[ElabError, CodeTable] =
    (operations(v, attached, written, kb), written.traverse(implemented(v, _))).mapN((ops, impls) =>
      CodeTable(attached ++ ops, impls.toMap))

  /** Each operation's meaning, its model's, written where its Scala is given (or the FrModel, with none). */
  private def operations(v: Vocabulary, attached: Map[SymbolName, Attachment], written: List[Operations],
      kb: Option[RelPath]): ValidatedNec[ElabError, List[(SymbolName, Attachment)]] =
    v.models.flatMap(m => m.ops.map(o => o.op -> m.name)).groupMap(_._1)(_._2).toList.traverse { (op, ms) =>
      val at = written.find(_.definitions.contains(op)).map(_.writtenIn).orElse(kb)
      if ms.distinct.size > 1 then ElabError(Site.Meaning(op), Fault.MeantByTwo(op.value, ms.map(_.value))).invalidNec
      else if attached.contains(op) then ElabError(Site.Meaning(op), Fault.ModelledElsewhere(op.value)).invalidNec
      else at.map(p => op -> Attachment(Code.Modelled(ms.head), p)).toList.validNec
    }.map(_.flatten)

  /** The Scala given operations, under their model: exactly its operations. */
  private def implemented(v: Vocabulary, o: Operations): ValidatedNec[ElabError, (ModelName, Implementation)] =
    o.definitions.map(v.modelOf).distinct match
      case List(Some(m)) =>
        val missing = m.ops.map(_.op).filterNot(o.definitions.contains)
        if missing.isEmpty then (m.name -> o.implementation).validNec
        else ElabError(Site.Model(m.name), Fault.OperationsMissing(m.name.value, missing.map(_.value))).invalidNec
      case _             =>
        ElabError(Site.Meaning(o.definitions.head), Fault.NotOneModel(o.definitions.map(_.value))).invalidNec
