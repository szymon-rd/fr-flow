package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.expr.Exprs
import frflow.core.name.{DefName, SymbolName}
import frflow.core.vocab.ValueKind
import frflow.core.Theory

/** The calling rule of the two kinds of values (owner §15), where the types cannot enforce it. The DSL's types
  * already keep a Declaration out of code: only a Definition takes code (`implementProven`, `implementTested`,
  * `implementValue`, `provided`), plain code reads only Definitions (`env(d)`), and a Declaration is applied only
  * where a statement is being written (`Stating`). What remains: every Definition gets a meaning, and no Declaration
  * is reached from code through a define written outside a statement.
  */
object Meanings:
  def problems(t: Theory): ValidatedNec[Problem, Unit] =
    NonEmptyChain.fromSeq(undefined(t) ++ declarationsInCode(t)).fold(Validated.validNec(()))(Validated.invalid)

  /** A Definition with no code, no program, no value. A `define` is its own meaning (a define, not a symbol). */
  private def undefined(t: Theory): List[Problem] = t.vocabulary.symbols.collect {
    case s if s.kind == ValueKind.Definition && !t.code.attached.contains(s.name) => Problem.Undefined(s.name)
  }

  private def declarationsInCode(t: Theory): List[Problem] =
    t.code.attached.values.toList.flatMap(_.code.proven).distinct.flatMap(d => reached(t, d).map((at, s) =>
      Problem.DeclarationInCode(at, s))).distinct

  /** The Declarations a define mentions, and those of every define it calls, each with the define mentioning it. */
  private def reached(t: Theory, d: DefName): List[(DefName, SymbolName)] =
    t.vocabulary.closure(List(d)).flatMap(x =>
      Exprs.mentions(x.lambda.body).symbols.filter(Constrained.isDeclaration(t, _)).map(x.name -> _))
