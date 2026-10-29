package frflow.core

import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Progs}
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.spec.Statement
import frflow.core.vocab.{Define, Symbol, SymbolType, Vocabulary}

/** A program's errors, read off its steps, in two senses. The monad's: every error it raises, handles or meets (a
  * failing model's), one type, what its run in Lean is over (`ExceptT E`) and its type says (`Ty.FlowOf`). What
  * escapes: those it raises or meets outside a handler of that type (`Progs.failsWith`), what a failing run's clause
  * is of. And the theory with each program's monad error in its type: what a front end cannot know where a
  * Definition is written, since its code is given later. Only a proven program has errors; a Definition of a
  * program type given plain Scala, or none, has the error its type declares (none, from the DSL).
  */
object Failing:
  /** The error types a define's steps raise, handle or meet; none of a define that is no program. */
  def of(v: Vocabulary, d: Define): List[Ty] = d.lambda.body match
    case Expr.Do(p, _) =>
      (Progs.errors(p) ++ Progs.operations(p).flatMap(v.modelOf).flatMap(_.failsWith)).distinct
    case _             => Nil

  /** The error types a define's steps may end in. */
  def escaping(v: Vocabulary, d: Define): List[Ty] = d.lambda.body match
    case Expr.Do(p, _) => Progs.failsWith(p, v.modelOf(_).flatMap(_.failsWith))
    case _             => Nil

  /** The error types a run of a program Definition may end in: its proven program's, or its type's without one. */
  def escapingOf(t: Theory, op: SymbolName): List[Ty] = proven(t, op).fold(declared(t, op))(escaping(t.vocabulary, _))

  /** The error types a program Definition's run is over: its proven program's, or its type's without one. */
  def ofDefinition(t: Theory, op: SymbolName): List[Ty] = proven(t, op).fold(declared(t, op))(of(t.vocabulary, _))

  private def proven(t: Theory, op: SymbolName): Option[Define] = t.code.attached.get(op).map(_.code).collect {
    case Code.ProvenFlow(f) => f
  }.flatMap(t.vocabulary.define)

  private def declared(t: Theory, op: SymbolName): List[Ty] = t.vocabulary.symbol(op).map(_.ty).toList.flatMap {
    case SymbolType.Typed(ty) => Ty.errorOf(ty).toList
    case _                    => Nil
  }

  /** Each program's define typed with its monad's error, and each Definition a program is the meaning of; a program
    * over two error types is left with none (`Validate` refuses it, `ErrorsDiffer`).
    */
  def typed(t: Theory): Theory =
    val v = t.vocabulary
    val symbols = v.symbols.map(s => (s.ty, t.code.attached.get(s.name).map(_.code)) match
      case (SymbolType.Typed(ty), Some(Code.ProvenFlow(_))) =>
        s.copy(ty = SymbolType.Typed(Ty.failing(ty, one(ofDefinition(t, s.name)))))
      case _                                                => s)
    val types = symbols.collect { case Symbol(n, _, SymbolType.Typed(ty), _) => n -> ty }.toMap.get
    val defines = v.defines.map(d => d.copy(written = d.written.failing(one(of(v, d))).retypedBody(types)))
    t.copy(vocabulary = v.copy(symbols = symbols, defines = defines),
      nodes = t.nodes.map(s => s.copy(node = s.node.copy(statement = retyped(s.node.statement, types)))))

  /** A statement's formula with its programs at the types their code gives them: what a formula's IR says of a
    * program (`Exprs.typeOf`) is its resolved type, and its posts' too.
    */
  private def retyped(s: Statement, types: SymbolName => Option[Ty]): Statement = s match
    case Statement.Claim(f, r)   => Statement.Claim(f.retyped(types), r)
    case Statement.Assumption(f) => Statement.Assumption(f.retyped(types))
    case design                  => design

  /** The failing runs' clauses a formula states (`.failing`, `.failsChangingNothing[E]`): the program each is about,
    * and the clause's type.
    */
  def clauses(formula: Expr): List[(SymbolName, Ty)] = Exprs.all(formula).collect {
    case Expr.Runs(run, _, true, error, _, _) => program(run).map(_ -> error.ty)
  }.flatten.distinct

  /** Whether a formula runs a program that is no Definition applied to its inputs (a define's result, a variable):
    * what such a run may fail with is no Definition's type, so Lean could not be told how to match it.
    */
  def runsNoDefinition(formula: Expr): Boolean = Exprs.all(formula).exists {
    case Expr.Runs(run, _, _, _, _, _) => program(run).isEmpty
    case _                             => false
  }

  private def program(run: Expr): Option[SymbolName] = run match
    case Expr.Sym(op, _)     => Some(op)
    case Expr.Apply(f, _, _) => program(f)
    case _                   => None

  private def one(errors: List[Ty]): Option[Ty] = errors match
    case List(e) => Some(e)
    case _       => None
