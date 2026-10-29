package frflow.core.typing

import frflow.core.expr.{Expr, Exprs, Iteration, OutsideFact, Pattern, PrimOp, Prog, Side, Value}
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.Selector
import frflow.core.ty.{DataType, Ty}

/** Whether one node of the IR is typed as its parts are (their types as `Exprs.typeOf` reads them): a constant by
  * its value, a symbol by the vocabulary, a call (of a define known) and an application by the function's
  * parameters, a record by its constructor's fields, a match by its patterns, an operator by its operands; a
  * program's step by the operation's signature and the model's state. A fact about the outside is no part of a term.
  */
final class Local(ctx: IrContext):
  private def ty(e: Expr): Ty = Exprs.typeOf(e)
  private def data(n: TypeName): Option[DataType] = ctx.data(n)

  def typed(e: Expr): Boolean = e match
    case Expr.Lit(v, t)               => fits(v, t)
    case Expr.Sym(n, t)               => ctx.symbols(n, t)
    case Expr.Call(d, as, t)          => ctx.defines(d).exists(applies(_, as, t))
    case Expr.Apply(f, as, t)         => as.nonEmpty && applies(ty(f), as, t)
    case Expr.Fun(l)                  => ty(l.body) == l.result
    case Expr.Quant(_, _, b)          => ty(b) == Ty.Bool
    case Expr.If(c, a, b)             => ty(c) == Ty.Bool && (ty(a) == ty(b) || raises(ty(a)) || raises(ty(b)))
    case Expr.Match(on, arms, t)      => arms.forall(a => (ty(a.body) == t || raises(ty(a.body))) &&
        matches(a.pattern, ty(on)))
    case Expr.Let(x, v, _)            => x.ty == ty(v)
    case Expr.Field(on, n, i, t)      => field(ty(on), n, i, t)
    case Expr.Copy(on, n, us)         => ty(on) == Ty.Data(n) && us.forall((i, v) => record(n).lift(i).contains(ty(v)))
    case Expr.Make(n, c, as)          => fields(n, c).forall(_ == as.map(ty))
    case Expr.Inject(s, a, t)         => t match
        case Ty.EitherOf(l, r) => ty(a) == (if s == Side.Error then l else r)
        case _                 => false
    case Expr.ListOf(es, t)           => es.forall(ty(_) == t)
    case e: Expr.Iterate              => iterate(e)
    case Expr.Fold(xs, z, acc, x, b)  => Ty.elementOf(ty(xs)).contains(x.ty) && acc.ty == ty(z) && ty(b) == ty(z)
    case Expr.Pairwise(xs, x, y, b)   => ty(xs) == Ty.ListOf(x.ty) && x.ty == y.ty && ty(b) == Ty.Bool
    case Expr.Prim(op, as, t)         => prim(op, as.map(ty), t)
    case Expr.Runs(_, w, _, _, a, b)  => ty(w) == Ty.World && a.ty == Ty.World && ty(b) == Ty.Bool
    case Expr.Part(w, _, _)           => ty(w) == Ty.World
    case Expr.Unchanged(a, b)         => ty(a) == Ty.World && ty(b) == Ty.World
    case Expr.Outside(_)              => false
    case Expr.Var(_) | Expr.Tuple(_) | Expr.SomeOf(_) | Expr.Do(_, _) => true // their type is their parts'

  /** A program's step typed by what it calls or changes: an operation's arguments and result, a model's state, a
    * branch's condition, what a loop or a handler binds.
    */
  def step(p: Prog[Expr]): Boolean = p match
    case Prog.Call(op, as, t) if op == Prog.leftWins => as.isEmpty && t == Ty.Bool
    case Prog.Call(op, as, t)               => ctx.operations(op).exists(s => s.params.map(_._2) == as.map(ty) &&
        s.result == t)
    case Prog.Read(m)                       => ctx.states(m).nonEmpty
    case Prog.Write(m, s)                   => ctx.states(m).contains(ty(s))
    case Prog.Modify(m, x, n)               => ctx.states(m).exists(st => x.ty == st && ty(n) == st)
    case Prog.Branch(c, _, _)               => ty(c) == Ty.Bool
    case Prog.Loop(o, x, _)                 => Ty.elementOf(ty(o)).contains(x.ty)
    case Prog.Collect(o, x, _)              => Ty.elementOf(ty(o)).contains(x.ty)
    case Prog.ParEach(o, x, _, _)           => Ty.elementOf(ty(o)).contains(x.ty)
    case Prog.Accumulate(o, z, acc, x, _)   => Ty.elementOf(ty(o)).contains(x.ty) && ty(z) == acc.ty
    case Prog.Catch(_, error, x, _)         => x.ty == error
    case _                                  => true

  /** A fact about the outside, said whole: of a model known, its initial rule a define on the model's state. */
  def fact(f: OutsideFact): Boolean = f match
    case OutsideFact.OnlyCodeChanges(m) => ctx.states(m).nonEmpty
    case OutsideFact.Atomic(m)          => ctx.states(m).nonEmpty
    case OutsideFact.Initially(m, d)    => ctx.states(m).exists(s => ctx.defines(d).contains(Ty.FnOf(List(s), Ty.Bool)))

  /** A constant's value of its type, each part of its part's type. */
  private def fits(v: Value, t: Ty): Boolean = (v, t) match
    case (Value.Bool(_), Ty.Bool)                 => true
    case (Value.Num(n), Ty.Num(k))                => k.holds(n)
    case (Value.Str(_), Ty.Str)                   => true
    case (Value.Unit, Ty.Unit)                    => true
    case (Value.Data(c, fs), Ty.Data(n))          => fields(n, c).exists(ts => ts.size == fs.size &&
        fs.zip(ts).forall(fits(_, _)))
    case (Value.Many(es), Ty.ListOf(a))           => es.forall(fits(_, a))
    case (Value.Many(es), Ty.SetOf(a))            => es.forall(fits(_, a))
    case (Value.Maybe(e), Ty.OptionOf(a))         => e.forall(fits(_, a))
    case (Value.Pairs(es), Ty.MapOf(k, w))        => es.forall((a, b) => fits(a, k) && fits(b, w))
    case (Value.Tuple(es), Ty.TupleOf(ts))        => es.size == ts.size && es.zip(ts).forall(fits(_, _))
    case (Value.Inject(s, e), Ty.EitherOf(l, r))  => fits(e, if s == Side.Error then l else r)
    case (Value.World(_, _), Ty.World)            => true
    case _                                        => false

  /** A branch that only raises, as a value or a program: it takes the other branch's type (`Ty.join`). */
  private def raises(t: Ty): Boolean = t match
    case Ty.Never | Ty.FlowOf(Ty.Never, _) => true
    case _                                 => false

  /** A function type applied to `as`, one argument at a time, each of its parameter's type, gives `t`; a program
    * applied to a world gives its run (`Ty.applied`).
    */
  private def applies(f: Ty, as: List[Expr], t: Ty): Boolean = (f, as) match
    case (_, Nil)                        => f == t
    case (Ty.FnOf(p :: _, _), a :: rest) => ty(a) == p && applies(Ty.applied(f), rest, t)
    case (Ty.FlowOf(_, _), a :: rest)    => ty(a) == Ty.World && applies(Ty.applied(f), rest, t)
    case _                               => false

  private def fields(n: TypeName, c: CtorName): Option[List[Ty]] =
    data(n).map(d => d.fieldsOf(c))

  /** The fields of a record (a copy names a record's, never a case's). */
  private def record(n: TypeName): List[Ty] = data(n).fold(Nil)(_.fieldTypes)

  /** A record's field, an enum's case's (the case's own record), or a pair's component (Lean's `Prod`, `p.1`). */
  private def field(on: Ty, n: TypeName, i: Int, t: Ty): Boolean = on match
    case Ty.TupleOf(ts) => n == Selector.pair && ts.lift(i).contains(t)
    case _              => on == Ty.Data(n) && data(n).exists(d => d match
        case DataType.Product(_, _, fs) => fs.lift(i).exists(_.ty == t)
        case DataType.Sum(_, _, cs)     => cs.exists(_.fields.lift(i).exists(_.ty == t)))

  /** A pattern takes apart a value of its type, binding each part at the part's type. */
  private def matches(p: Pattern, on: Ty): Boolean = (p, on) match
    case (Pattern.Ctor(n, c, xs), Ty.Data(m))      => n == m && fields(n, c).forall(_ == xs.map(_.ty))
    case (Pattern.SomeP(x), Ty.OptionOf(a))        => x.ty == a
    case (Pattern.NoneP, Ty.OptionOf(_))           => true
    case (Pattern.Outcome(s, x), Ty.EitherOf(e, a)) => x.ty == (if s == Side.Error then e else a)
    case (Pattern.ConsP(h, t), Ty.ListOf(a))       => h.ty == a && t.ty == on
    case (Pattern.NilP, Ty.ListOf(_))              => true
    case _                                         => false

  /** Over a list's elements, or an option's (only whether all or any meets the body). */
  private def iterate(e: Expr.Iterate): Boolean =
    val (how, on, x, body, t) = (e.how, ty(e.over), e.x.ty, ty(e.body), e.ty)
    val over = on == Ty.ListOf(x) || on == Ty.SetOf(x) ||
      (on == Ty.OptionOf(x) && Set(Iteration.Forall, Iteration.Exists)(how))
    over && (how match
      case Iteration.Forall | Iteration.Exists    => body == Ty.Bool && t == Ty.Bool
      case Iteration.Filter | Iteration.FilterNot => body == Ty.Bool && t == on
      case Iteration.Find                         => body == Ty.Bool && t == Ty.OptionOf(x)
      case Iteration.Map                          => Ty.elementOf(t).contains(body)
      case Iteration.FlatMap                      => t == body && Ty.elementOf(body).nonEmpty)

  private def prim(op: PrimOp, as: List[Ty], t: Ty): Boolean = op match
    case PrimOp.And | PrimOp.Or | PrimOp.Implies | PrimOp.Not => t == Ty.Bool && as.forall(_ == Ty.Bool)
    case PrimOp.Eq | PrimOp.Ne                                 => t == Ty.Bool && as.distinct.size == 1
    case PrimOp.Lt | PrimOp.Le | PrimOp.Gt | PrimOp.Ge         => t == Ty.Bool && numbers(as)
    case PrimOp.Add | PrimOp.Sub | PrimOp.Mul | PrimOp.Div | PrimOp.Mod | PrimOp.Max | PrimOp.Min | PrimOp.Neg =>
      numbers(as) && as.headOption.contains(t)
    case PrimOp.Length                                         => numbers(List(t)) && as.forall(holding)
    case PrimOp.Nodup                                          => t == Ty.Bool && as.forall(holding)
    case PrimOp.Cons                                           => as == List(Ty.elementOf(t).getOrElse(t), t)
    case PrimOp.Append                                         => as.forall(_ == t)
    case PrimOp.Contains                                       =>
      t == Ty.Bool && as.headOption.flatMap(Ty.elementOf) == as.lift(1)
    case PrimOp.IsEmpty | PrimOp.NonEmpty                      => t == Ty.Bool && as.forall(holding)
    case PrimOp.Zip                                            => t == Ty.ListOf(Ty.TupleOf(as.flatMap(Ty.elementOf)))
    case PrimOp.GetOrElse                                      => as == List(Ty.OptionOf(t), t)
    case PrimOp.Get | PrimOp.GetOrElseAt | PrimOp.Updated      => keyed(op, as, t)
    case PrimOp.Incl                                           => as == List(t, Ty.elementOf(t).getOrElse(t))
    case PrimOp.Union                                          => as == List(t, t)
    case _                                                     => true

  private def numbers(as: List[Ty]): Boolean = as.nonEmpty && as.distinct.size == 1 && as.forall {
    case Ty.Num(_) => true
    case _         => false
  }

  private def holding(t: Ty): Boolean = Ty.elementOf(t).nonEmpty

  /** A map's operations: its value at a key (an option), that or a default, the map with the key's value replaced. */
  private def keyed(op: PrimOp, as: List[Ty], t: Ty): Boolean = (op, as) match
    case (PrimOp.Get, List(Ty.MapOf(k, v), key))            => k == key && t == Ty.OptionOf(v)
    case (PrimOp.GetOrElseAt, List(Ty.MapOf(k, v), key, d)) => k == key && v == d && t == d
    case (PrimOp.Updated, List(m, k, v))                    => m == t && t == Ty.MapOf(k, v)
    case _                                                  => false
