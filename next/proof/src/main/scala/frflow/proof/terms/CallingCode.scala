package frflow.proof.terms

import frflow.core.analysis.outside.{Guards, Reads}
import frflow.core.code.Code
import frflow.core.expr.{Binder, Expr}
import frflow.core.name.{DefName, SourceText, SymbolName, VarId}
import frflow.core.spec.{Form, Written}
import frflow.core.term.{Bound, Sym}
import frflow.core.term.interpret.{Guard, Guarded, ToExpr}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** Proven code calling Definitions given plain Scala (owner §37): the Definition it stands in, its code, the
  * arguments' types of each such call, in order, and what `made_<code>_call_<i>` states of a rule at call `i`: for
  * every input meeting what always holds of its type, and each value before the call (a call's result, an element)
  * meeting its type's, the rule of each argument it reaches, on every path to the call. A program's hypotheses take
  * the rules of the states it reads only (owner §33).
  */
final case class CallingCode(definition: SymbolName, code: DefName, calls: List[List[Ty]],
    formula: (Int, Guard) => Written[Expr])

object CallingCode:
  def of(t: Theory): List[CallingCode] =
    val scala = t.code.attached.collect { case (d, a) if a.code.scala.nonEmpty => d }.toSet
    val ops = t.vocabulary.models.flatMap(_.sigs).map(o => o.name -> o.params.map(_._2)).toMap
    t.code.attached.toList.sortBy(_._1.value).flatMap((d, a) => a.code match
      case Code.Proven(c)     => t.vocabulary.define(c).map(coded(d, _, Guards.byAlways(t).map(_._2))(
          [T[_]] => (s: Sym[T], env: Map[VarId, T[Any]]) => body(s, scala, env, _)))
      case Code.ProvenFlow(f) => t.vocabulary.define(f).map(coded(d, _, Guards.reading(t, Reads.ofProgram(t, d))
          .map(_._2))([T[_]] => (s: Sym[T], env: Map[VarId, T[Any]]) => CallSites(s, scala, ops).of(env)))
      case _                  => None).filter(_.calls.nonEmpty)

  private type Read = [T[_]] => (Sym[T], Map[VarId, T[Any]]) => Define => List[AtCall[T]]

  private def coded(d: SymbolName, define: Define, guards: List[Guard])(read: Read): CallingCode =
    val inputs = define.lambda.params
    val calls = read[ToExpr.IR](ToExpr, inputs.map(x => x.id -> ToExpr.free[Any](x)).toMap)(define).map(_.tys)
    CallingCode(d, define.name, calls, (i, kept) => Written.formula(Guarded.of([T[_]] => (s: Sym[T]) =>
      over(s, inputs, Map.empty)(env => read[T](s, env)(define).lift(i).fold(s.bool(true))(_.stated(kept))),
      guards), SourceText(s"call ${i + 1} of plain Scala in ${define.name.value}")))

  /** Every value of each input, bound for the code's terms. */
  private def over[T[_]](s: Sym[T], inputs: List[Binder], env: Map[VarId, T[Any]])(
      k: Map[VarId, T[Any]] => T[Boolean]): T[Boolean] = inputs match
    case x :: rest => s.forall(Bound[Any](x.hint, x.ty))(v => over(s, rest, env + (x.id -> v))(k))
    case Nil       => k(env)

  private def body[T[_]](s: Sym[T], scala: Set[SymbolName], env: Map[VarId, T[Any]], d: Define): List[AtCall[T]] =
    d.written.form match
      case Form.Term(term) => Calls.of(s, scala, env)(term).calls
      case Form.Steps(_)   => Nil
