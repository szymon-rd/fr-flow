package frflow.eval.run

import frflow.core.analysis.Resolve
import frflow.core.code.{Code, Impl, Values}
import frflow.core.example.Given
import frflow.core.expr.{Exprs, Lambda}
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.{Form, Written}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Fn, Semantics}

/** The values code reads, made explicitly for the examples and the generated tests (there is no ambient scope): the
  * meaning of each Definition with one (its plain Scala, its proven code run by the evaluator, its fixed value), and
  * the values given (an example's, a test's drawn values, production's), which win. A `define` is run by the
  * evaluator wherever it is called: there is nothing to wire for it. A proven program runs through `Running` in
  * production, where its value is none (`NotEvaluated(Steps)`); in the examples and tests (`Wiring.onModels`) its
  * value is its run on the models (`ProgramRun`).
  */
final class Wiring(semantics: Semantics, t: Theory, programs: Programs):
  def this(semantics: Semantics, t: Theory) = this(semantics, t, Programs.Run)

  def values(supplied: Values): Values =
    lazy val all: Values = Values(meanings(() => all)) ++ supplied
    all

  /** The values given (an example's, production's), each as Scala holds it, typed by its declaration. */
  def supplied(gs: List[Given]): Values = Values(gs.map(g => g.symbol -> held(g)).toMap)

  /** What a test of `node`'s Definition needs given that wiring does not make, as today's `needed`: what its
    * statement reads (itself or through its defines) and what its code calls; not its own Definition, nor one with a
    * meaning wiring makes.
    */
  def needed(node: NodeId): List[SymbolName] =
    val own = t.node(node).flatMap(_.statement.definition)
    val made = meanings(() => Values.none).keySet
    (Resolve.mentions(t, node).symbols ++ own.toList.flatMap(reads)).distinct.filterNot(s => own.contains(s) || made(s))

  /** Each Definition with a meaning wiring can make: plain code, its proven define run by `Semantics`, its value;
    * and each define plain code says it calls (`implementTested(c, define)`), run by `Semantics`, read as `env(d)`.
    */
  private def meanings(values: () => Values): Map[SymbolName, () => Any] =
    (calledDefines ++ t.code.attached.toList.flatMap((d, a) => runs(d, a.code).map(d -> _)))
      .map((d, impl) => d -> (() => impl.make(values()))).toMap

  private def calledDefines: List[(SymbolName, Impl)] = t.code.attached.values.toList.flatMap(_.code match
    case Code.Tested(_, calls) => calls
    case _                     => Nil).distinct.flatMap(s => t.vocabulary.define(DefName(s.value)).map(x =>
    s -> written(x.written)))

  /** The code a Definition runs as: its plain code, its proven define, or its fixed value. */
  private def runs(d: SymbolName, code: Code): Option[Impl] = code match
    case Code.Valued(v) => typeOf(d).map(ty => Impl(0, _ => Fn.ref(semantics.literal(v, ty))))
    case Code.Provided  => None
    case other          =>
      other.scala.map(_.impl).orElse(other.proven.flatMap(t.vocabulary.define).map(x => written(x.written)))

  /** A define's code: run by the evaluator; a program's, its run on the models where `programs` says so. */
  private def written(w: Written[Lambda]): Impl = w.form match
    case Form.Steps(steps) if programs == Programs.OnModels => ProgramRun.impl(semantics, t.vocabulary, w, steps)
    case _                                                  => proven(w)

  private def held(g: Given): () => Any =
    val v = semantics.literal(g.value, typeOf(g.symbol).getOrElse(Ty.Unit)).unwrap
    () => v

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

object Wiring:
  /** The values of the examples and the generated tests: a proven program's value its run on the models. */
  def onModels(semantics: Semantics, t: Theory): Wiring = Wiring(semantics, t, Programs.OnModels)
