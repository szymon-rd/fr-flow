package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.analysis.resolution.Constrained
import frflow.core.expr.Exprs
import frflow.core.name.{DefName, SymbolName}
import frflow.core.Theory
import frflow.core.vocab.ValueKind

/** The calling rule of the two kinds of values (owner §15). In the DSL every word is a Declaration; here a word
  * is of the kind Definition when the model gives it a meaning (a Definition of it: `define`, `defineTested`,
  * `defineValue`, `provided`) or its code calls it, and of the kind Declaration when only statements read it. A
  * `stated` define's body is a statement's, which code cannot call. What remains to check: every word code calls
  * gets a meaning or is assumed, and no word of the kind Declaration is reached from code through a define.
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
