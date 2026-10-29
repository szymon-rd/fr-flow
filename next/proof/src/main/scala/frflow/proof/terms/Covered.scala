package frflow.proof.terms

import frflow.core.code.Code
import frflow.core.expr.{Prog, Progs}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** What a reading of proven code for its calls knows of the Definitions it calls: those given plain Scala, whose
  * arguments are checked at the call (`scala`); those whose proven code is a define, read in place on the arguments
  * they are given (`proven`, owner §37: a value handed on through proven code reaches the plain Scala it calls); and
  * the models' operations (`operations`).
  */
final case class Covered(scala: Set[SymbolName], proven: Map[SymbolName, Define],
    operations: Map[SymbolName, Covered.Operation])

object Covered:
  /** An operation on a state: its model, its inputs' types, whether its meaning writes the state. */
  final case class Operation(model: ModelName, inputs: List[Ty], writes: Boolean)

  def of(t: Theory): Covered = Covered(
    t.code.attached.collect { case (d, a) if a.code.scala.nonEmpty => d }.toSet,
    t.code.attached.toList.flatMap((d, a) => a.code match
      case Code.Proven(c) => t.vocabulary.define(c).map(d -> _)
      case _              => None).toMap,
    t.vocabulary.models.flatMap(m => m.ops.map(o => o.op -> Operation(m.name, o.params.map(_.ty),
      Progs.all(o.steps).exists { case Prog.Write(_, _) | Prog.Modify(_, _, _) => true; case _ => false }))).toMap)
