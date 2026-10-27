package frflow.core

import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Progs}
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, SymbolType, Vocabulary}

/** The error a program may fail with, read off its steps (`Progs.failsWith`: what it raises and the failing
  * boundaries it calls, outside a handler of that type), and the theory with each program's error in its type
  * (`Ty.FlowOf`): what a front end cannot know where a Definition is written, since its code is given later.
  */
object Failing:
  /** The error types a define's steps may end in; none of a define that is no program. */
  def of(v: Vocabulary, d: Define): List[Ty] = d.lambda.body match
    case Expr.Do(p, _) => Progs.failsWith(p, v.boundary(_).flatMap(_.failsWith))
    case _             => Nil

  /** The error types a run of a program Definition may end in: its proven program's, or its type's without one. */
  def ofDefinition(t: Theory, op: SymbolName): List[Ty] =
    t.code.attached.get(op).map(_.code) match
      case Some(Code.ProvenFlow(f)) => t.vocabulary.define(f).toList.flatMap(of(t.vocabulary, _))
      case _                        => t.vocabulary.symbol(op).map(_.ty).toList.flatMap {
          case SymbolType.Typed(ty) => Ty.errorOf(ty).toList
          case _                    => Nil
        }

  /** Each program's define typed with its error, and each Definition a program is the meaning of; a program that may
    * fail with two types is left with none (`Validate` refuses it, `ErrorsDiffer`).
    */
  def typed(t: Theory): Theory =
    val v = t.vocabulary
    val defines = v.defines.map(d => d.copy(written = d.written.failing(one(of(v, d)))))
    val symbols = v.symbols.map(s => (s.ty, t.code.attached.get(s.name).map(_.code)) match
      case (SymbolType.Typed(ty), Some(Code.ProvenFlow(_))) =>
        s.copy(ty = SymbolType.Typed(Ty.failing(ty, one(ofDefinition(t, s.name)))))
      case _                                                => s)
    t.copy(vocabulary = v.copy(symbols = symbols, defines = defines))

  /** The failing runs' clauses a formula states (`.failing`, `.failsChangingNothing[E]`): the program each is about,
    * and the clause's type.
    */
  def clauses(formula: Expr): List[(SymbolName, Ty)] = Exprs.all(formula).collect {
    case Expr.Runs(run, _, true, error, _, _) => program(run).map(_ -> error.ty)
  }.flatten.distinct

  private def program(run: Expr): Option[SymbolName] = run match
    case Expr.Sym(op, _)     => Some(op)
    case Expr.Apply(f, _, _) => program(f)
    case _                   => None

  private def one(errors: List[Ty]): Option[Ty] = errors match
    case List(e) => Some(e)
    case _       => None
