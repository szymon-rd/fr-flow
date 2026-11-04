package frflow.core.spec

import frflow.core.expr.{Binder, Expr, Exprs, Lambda, PrimOp, Quantifier}
import frflow.core.name.SymbolName
import frflow.core.term.{Final, Sym}
import frflow.core.term.interpret.Opened
import frflow.core.ty.Ty

/** A formula read as a run of a program from the world before (its success side the post, its failing side the
  * failure clause), or as a call of one Definition on its leading variables (the one so applied and mentioned
  * nowhere else, or, of several, the one on the left of the formula's equation). Nothing else changes how it is
  * read: every Definition and Declaration it mentions is constrained by it either way.
  */
object CallForms:
  def of(f: Written[Expr]): Option[CallForm] =
    val (xs, body) = leading(f.value)
    run(f, xs, body).orElse(call(f, xs, body))

  /** The formula read whole, as tests evaluate a claim that reads as no call: a lambda over its leading variables. */
  def whole(f: Written[Expr]): Written[Lambda] =
    val (xs, _) = leading(f.value)
    opened(f, xs, xs.size, None)

  private def run(f: Written[Expr], xs: List[Binder], body: Expr): Option[CallForm] =
    val runs = body match
      case r @ Expr.Runs(_, _, _, _, _, _)                                        => List(r)
      case Expr.Prim(PrimOp.And, List(a @ Expr.Runs(_, _, false, _, _, _), b @ Expr.Runs(_, _, true, _, _, _)), _) =>
        List(a, b)
      case _                                                                      => Nil
    for
      before <- xs.lastOption
      op     <- runs.headOption.flatMap(r => applied(r.run, xs.init))
      if runs.forall(r => r.before == Expr.Var(before) && applied(r.run, xs.init).contains(op))
      post   <- side(xs.init.size, op, false)(f)
    yield CallForm.Run(op, post, side(xs.init.size, op, true)(f).map(p =>
      FailureClause(p.value.params.reverse.drop(2).head.ty, p)))

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
    chosen.map((op, k) => CallForm.Call(op, opened(f, xs.take(k), k, None)))

  /** One side of the run below the inputs and the world before, if the run has it and the post mentions the
    * Definition nowhere else.
    */
  private def side(n: Int, op: SymbolName, failing: Boolean)(f: Written[Expr]): Option[Written[Lambda]] =
    val (xs, rest) = leading(f.value, Some(n + 1))
    val runs = rest match
      case r @ Expr.Runs(_, _, _, _, _, _) => List(r)
      case Expr.Prim(PrimOp.And, rs, _)    => rs.collect { case r @ Expr.Runs(_, _, _, _, _, _) => r }
      case _                               => Nil
    runs.find(_.failing == failing).map(r => opened(f, xs.init ++ List(r.outcome, xs.last, r.after), n + 1,
      Some(failing))).filterNot(post => mentions(post.value, op))

  private def opened(f: Written[Expr], inputs: List[Binder], n: Int, run: Option[Boolean]): Written[Lambda] =
    val body: Final[Boolean] = [T[_]] => (s: Sym[T]) => Opened.of(f.term, n, s, run)
    Written.lambda(inputs, body, f.source)

  private def applied(p: Expr, inputs: List[Binder]): Option[SymbolName] = p match
    case Expr.Sym(op, _) if inputs.isEmpty                                       => Some(op)
    case Expr.Apply(Expr.Sym(op, _), args, _) if args == inputs.map(Expr.Var(_)) => Some(op)
    case _                                                                       => None

  private def overLeading(args: List[Expr], xs: List[Binder]): Boolean = args == xs.take(args.size).map(Expr.Var(_))

  /** Every application of `op` is to exactly the leading variables `xs`: a call's result stands for each. */
  private def overLeadingOnly(all: List[Expr], op: SymbolName, xs: List[Binder]): Boolean =
    all.collect { case Expr.Apply(Expr.Sym(`op`, _), args, _) => args }.forall(_ == xs.map(Expr.Var(_)))

  private def onlyApplied(all: List[Expr], op: SymbolName): Boolean =
    all.count { case Expr.Sym(`op`, _) => true; case _ => false } ==
      all.count { case Expr.Apply(Expr.Sym(`op`, _), _, _) => true; case _ => false }

  /** The variables of the leading `forall`s (all of them, or the first `n`), and what is below them. */
  private def leading(e: Expr, n: Option[Int] = None): (List[Binder], Expr) = (e, n) match
    case (_, Some(0))                                       => (Nil, e)
    case (Expr.Quant(Quantifier.Forall, List(x), body), _) =>
      val (xs, rest) = leading(body, n.map(_ - 1))
      (x :: xs, rest)
    case _                                                  => (Nil, e)

  private def mentions(post: Lambda, op: SymbolName): Boolean =
    Exprs.all(post.body).exists { case Expr.Sym(`op`, _) => true; case _ => false }
