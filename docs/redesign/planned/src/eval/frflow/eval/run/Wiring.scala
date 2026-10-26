package frflow.eval.run

import frflow.core.analysis.Resolve
import frflow.core.code.{Code, Impl, Values}
import frflow.core.expr.{Exprs, Lambda}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.Written
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Fn, Semantics}

/** The values code reads, made explicitly for the examples and the generated tests (there is no ambient scope): the
  * meaning of each Definition with one (its plain Scala, its proven code run by the evaluator, its fixed value), and
  * the values given (an example's, a test's drawn values, production's), which win. A `define` is run by the
  * evaluator wherever it is called: there is nothing to wire for it.
  */
final class Wiring(semantics: Semantics, t: Theory):
  def values(supplied: Values): Values =
    lazy val all: Values = Values(meanings(() => all)) ++ supplied
    all

  /** What a test of `node`'s Definition needs given that wiring does not make, as today's `needed`: what its
    * statement reads (itself or through its defines) and what its code calls; not its own Definition, nor one with a
    * meaning wiring makes.
    */
  def needed(node: NodeId): List[SymbolName] =
    val own = t.node(node).flatMap(_.statement.definition)
    val made = meanings(() => Values.none).keySet
    (Resolve.mentions(t, node).symbols ++ own.toList.flatMap(reads)).distinct.filterNot(s => own.contains(s) || made(s))

  /** Each Definition with a meaning wiring can make: plain code, its proven define run by `Semantics`, its value. */
  private def meanings(values: () => Values): Map[SymbolName, () => Any] =
    t.code.attached.toList.flatMap((d, a) => runs(d, a.code).map(impl => d -> (() => impl.make(values())))).toMap

  /** The code a Definition runs as: its plain code, its proven define, or its fixed value. */
  private def runs(d: SymbolName, code: Code): Option[Impl] = code match
    case Code.Valued(v) => typeOf(d).map(ty => Impl(0, _ => Fn.ref(semantics.literal(v, ty))))
    case Code.Provided  => None
    case other          =>
      other.scala.map(_.impl).orElse(other.proven.flatMap(t.vocabulary.define).map(x => proven(x.written)))

  private def typeOf(d: SymbolName): Option[Ty] =
    t.vocabulary.symbol(d).map(_.ty).collect { case SymbolType.Typed(ty) => ty }

  private def proven(w: Written[Lambda]): Impl =
    val f = semantics.lambda(w)
    Impl(w.value.arity, values => Fn.of[AnyRef](w.value.arity)(f.called(values)))

  /** What a Definition's code reads: the Definitions plain code calls, as attached; a define, what it mentions. */
  private def reads(op: SymbolName): List[SymbolName] = t.code.attached.get(op).map(_.code) match
    case Some(Code.Tested(_, calls)) => calls
    case Some(c)                     =>
      t.vocabulary.closure(c.proven.toList).flatMap(d => Exprs.mentions(d.lambda.body).symbols)
    case None                        => Nil
