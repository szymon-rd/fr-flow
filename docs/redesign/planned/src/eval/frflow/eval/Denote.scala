package frflow.eval

import cats.syntax.all.*
import frflow.core.code.Impl
import frflow.core.Elaborated
import frflow.core.expr.{Expr, Lambda, Value}
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.Ty

/** The Scala meaning of the term language. Law: Lean proves `e = v` exactly when `Denote(e)` gives `v`. */
final class Denote(e: Elaborated):
  private type Run = Env => Either[EvalError, ScalaValue]
  private val literals = Literals(e)
  private val reflected = Reflect(e)
  private lazy val bodies: Map[DefName, Run] =
    e.theory.vocabulary.defines.map(d => d.name -> compile(d.lambda.body)).toMap

  def apply(x: Expr): Compiled = Compiled(compile(x))
  def lambda(l: Lambda): Applied =
    val body = compile(l.body)
    Applied((env, args) => body(l.params.map(_.id).zip(args).foldLeft(env)((en, xv) => en.bind(xv._1, xv._2))))
  /** A define as code a running system calls (`implementProven`): a function of its inputs, typed by its arity. */
  def impl(d: DefName): Option[Impl] = e.theory.vocabulary.define(d).map(_.lambda).map { l =>
    val f = lambda(l)
    Impl(l.arity, () => Fn.of[AnyRef](l.arity)(f.called))
  }
  /** A constant as Scala holds it, and a Scala value as a constant: both by its type. */
  def literal(v: Value, t: Ty): ScalaValue = literals(v, t)
  def reflect(v: ScalaValue, t: Ty): Value = reflected(v, t)

  private def compile(x: Expr): Run = x match
    case Expr.Var(v)            => env => env.variables.get(v.id).toRight(EvalError.Unbound(SymbolName(v.hint)))
    case Expr.Lit(v, t)         => val s = literals(v, t); _ => Right(s)
    case Expr.Sym(n, _)         => env => env.symbols(n).toRight(EvalError.Unbound(n))
    case Expr.Quant(_, _, _)    => _ => Left(EvalError.Quantified)
    case Expr.If(c, a, b)       => branch(compile(c), compile(a), compile(b))
    case Expr.Call(d, as, _)    => call(d, as.map(compile))
    case Expr.Prim(op, as, _)   => DenotePrim(op, as.map(compile))
    case _                      => ??? // every other case, one line each, as today's `Eval.compile`

  private def branch(c: Run, a: Run, b: Run): Run = env => c(env).flatMap(v => if Fn.bool(v) then a(env) else b(env))

  private def call(d: DefName, args: List[Run]): Run =
    val params = e.theory.vocabulary.define(d).toList.flatMap(_.lambda.params.map(_.id))
    env => bodies.get(d).toRight(EvalError.NoDefine(d)).flatMap(body =>
      args.traverse(_(env)).flatMap(vs => body(params.zip(vs).foldLeft(env)((en, p) => en.bind(p._1, p._2)))))
