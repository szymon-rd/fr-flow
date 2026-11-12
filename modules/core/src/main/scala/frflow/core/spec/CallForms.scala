package frflow.core.spec

import frflow.core.expr.{Binder, Expr, Exprs, Lambda, PrimOp, Quantifier}
import frflow.core.name.SymbolName
import frflow.core.term.interpret.Opened
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A formula read as a call of one Definition on its leading variables (the one so applied and mentioned nowhere
  * else, or, of several, the one on the left of the formula's equation). Nothing else changes how it is read: every
  * Definition and Declaration it mentions is constrained by it either way.
  */
object CallForms:
  def of(f: Written[Expr]): Option[CallForm] =
    val (xs, body) = leading(f.value)
    call(f, xs, body)

  /** The formula read whole, as tests evaluate a claim that reads as no call: a lambda over its leading variables. */
  def whole(f: Written[Expr]): Written[Lambda] =
    val (xs, _) = leading(f.value)
    opened(f, xs, xs.size)

  private def call(f: Written[Expr], xs: List[Binder], body: Expr): Option[CallForm] =
    val all = Exprs.all(body)
    val candidates = all.collect {
      case Expr.Apply(Expr.Sym(op, Ty.FnOf(_, _)), args, _) if args.nonEmpty && overLeading(args, xs) => (op, args.size)
    }.distinct.filter((op, k) => onlyApplied(all, op) && overLeadingOnly(all, op, xs.take(k)))
    val chosen = candidates match
      case List(one) => Some(one)
      case several   => body match
        case Expr.Prim(PrimOp.Eq, List(Expr.Apply(Expr.Sym(op, _), _, _), _), _) => several.find(_._1 == op)
        case _                                                                   => None
    chosen.map((op, k) => CallForm(op, opened(f, xs.take(k), k)))

  private def opened(f: Written[Expr], inputs: List[Binder], n: Int): Written[Lambda] =
    val body: Final[Boolean] = [T[_]] => (s: Sym[T]) => Opened.of(f.term, n, s)
    Written.lambda(inputs, body, f.source)

  private def overLeading(args: List[Expr], xs: List[Binder]): Boolean = args == xs.take(args.size).map(Expr.Var(_))

  /** Every application of `op` is to exactly the leading variables `xs`: a call's result stands for each. */
  private def overLeadingOnly(all: List[Expr], op: SymbolName, xs: List[Binder]): Boolean =
    all.collect { case Expr.Apply(Expr.Sym(`op`, _), args, _) => args }.forall(_ == xs.map(Expr.Var(_)))

  private def onlyApplied(all: List[Expr], op: SymbolName): Boolean =
    all.count { case Expr.Sym(`op`, _) => true; case _ => false } ==
      all.count { case Expr.Apply(Expr.Sym(`op`, _), _, _) => true; case _ => false }

  /** The variables of the leading `forall`s, and what is below them. */
  private def leading(e: Expr): (List[Binder], Expr) = e match
    case Expr.Quant(Quantifier.Forall, List(x), body) =>
      val (xs, rest) = leading(body)
      (x :: xs, rest)
    case _                                            => (Nil, e)
