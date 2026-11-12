package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term as Rocq, Ty}

/** The methods of Scala's library that are read: `Option`, `Some`, `Left` and `Right` made; a list's `::`, `head`,
  * `tail`, `isEmpty` and `foreach`; a `Set[Thread]`'s `empty`, `contains` and `+`; `==`, `!=`, `!`, `||` and `&&`;
  * `asInstanceOf`.
  *
  * `a || b` with an effect in `b` is `if a then ret true else b`. `==` is the equality of the type the values are
  * read at: of thread ids and of handles (`Nat.eqb`), of integers (`Z.eqb`), of exceptions (`exn_eqb`); against an
  * object of `obj`, the test that a `val` is it (`is_<name>`).
  */
private[threads] trait ReadData extends ReadOps:
  import q.reflect.*

  /** `list.foreach(fn)` (`ReadClosures`). */
  def foreach(list: Term, fn: Term)(using Env): Res

  private val list = "scala.collection.immutable.List"
  private val set = "scala.collection.immutable.Set"

  private def isA(t: Term, cls: String): Boolean = bases(plain(t.tpe).typeSymbol).exists(_.fullName == cls)

  def data(c: Call)(using Env): Option[Res] =
    built(c).orElse(c.on.flatMap(on => logic(c, on).orElse(listed(c, on)).orElse(threads(c, on))))

  private def built(c: Call)(using Env): Option[Res] =
    (c.symbol.owner.fullName.stripSuffix("$"), c.name, c.args) match
      case ("scala.Option", "apply", List(a))      =>
        val v = value(expr(a))
        Some(v.ty match
          case Ty.Of("option", _) => v
          case of                 => v.copy(term = Rocq.of("Some", v.term), ty = Ty.option(of)))
      case ("scala.Some", "apply", List(a))        => Some(wrapped("Some", a, Ty.option(_)))
      case ("scala.util.Right", "apply", List(a))  => Some(wrapped("inr", a, Ty.Sum(Ty.Never, _)))
      case ("scala.util.Left", "apply", List(a))   => Some(wrapped("inl", a, Ty.Sum(_, Ty.Never)))
      case (_, "empty", Nil) if c.on.exists(_.symbol.name == "Set") && c.types.map(of) == List(Some(Ty.Tid)) =>
        Some(Res.value(Rocq.At("nil", Ty.Tid), Ty.list(Ty.Tid)))
      case _                                       => None

  private def of(t: TypeRepr): Option[Ty] = scala.util.Try(repr(t)).toOption

  private def wrapped(ctor: String, a: Term, ty: Ty => Ty)(using Env): Res =
    val v = value(expr(a))
    v.copy(term = Rocq.of(ctor, bare(v.term)), ty = ty(v.ty))

  private def logic(c: Call, on: Term)(using Env): Option[Res] = (c.name, c.args) match
    case ("unary_!", Nil)                         => Some(applied("negb", List(expr(on)), Ty.Bool, Res.Kind.Value))
    case ("==" | "eq", List(b))                   => Some(equal(on, b))
    case ("!=" | "ne", List(b))                   => Some(applied("negb", List(equal(on, b)), Ty.Bool, Res.Kind.Value))
    case ("||", List(b))                          => Some(either(on, b, "orb", Rocq.Ref("true")))
    case ("&&", List(b))                          => Some(either(on, b, "andb", Rocq.Ref("false")))
    case ("asInstanceOf" | "$asInstanceOf$", Nil) => c.types.headOption.map(t => coerce(expr(on), repr(t)))
    case _                                        => None

  private def isNull(t: Term): Boolean = t match
    case Literal(NullConstant()) => true
    case _                       => false

  private def equal(a: Term, b: Term)(using Env): Res = singleton(b).orElse(singleton(a)) match
    case _ if isNull(a) || isNull(b) => refuse("a test for null that no branch is taken on")
    case Some((owner, name)) =>
      val other = if singleton(b).nonEmpty then a else b
      applied(catalogue.is(owner, name), List(coerce(expr(other), Ty.Val)), Ty.Bool, Res.Kind.Value)
    case None                =>
      val left = value(expr(a))
      val eqb = left.ty match
        case Ty.Tid | Ty.Nat => "Nat.eqb"
        case Ty.Z            => "Z.eqb"
        case Ty.Exn          => "exn_eqb"
        case other           => refuse(s"the equality of values of type $other")
      applied(eqb, List(left, coerce(expr(b), left.ty)), Ty.Bool, Res.Kind.Value)

  /** `a || b` and `a && b`: `b` is evaluated only where `a` does not decide. */
  private def either(a: Term, b: Term, both: String, decided: Rocq)(using Env): Res =
    val left = value(coerce(expr(a), Ty.Bool))
    val right = coerce(expr(b), Ty.Bool)
    if right.isValue && right.steps.isEmpty then
      Res(left.steps, Rocq.of(both, left.term, right.term), Ty.Bool, Res.Kind.Value)
    else if both == "orb" then
      Res(left.steps, Rocq.If(left.term, Rocq.ret(decided), right.program), Ty.Bool, Res.Kind.Program)
    else Res(left.steps, Rocq.If(left.term, right.program, Rocq.ret(decided)), Ty.Bool, Res.Kind.Program)

  private def listed(c: Call, on: Term)(using Env): Option[Res] =
    def of: Ty = reprOf(on) match
      case Some(Ty.Of("list", item)) => item
      case _                         => refuse("a list of a type that is not read")
    if !isA(on, list) then None
    else (c.name, c.args) match
      case ("::", List(head))    => Some(applied("cons", List(coerce(expr(head), of), expr(on)), Ty.list(of),
        Res.Kind.Value))
      case ("head", Nil)         => Some(applied("List_head", List(held(on)), of, Res.Kind.Program))
      case ("tail", Nil)         => Some(applied("List_tail", List(held(on)), Ty.list(of), Res.Kind.Program))
      case ("isEmpty", Nil)      => Some(applied("List_isEmpty", List(held(on)), Ty.Bool, Res.Kind.Value))
      case ("foreach", List(fn)) => Some(foreach(on, fn))
      case _                     => None

  /** A list read where it must be one: not null. */
  private def held(list: Term)(using Env): Res =
    val r = expr(list)
    r.ty match
      case Ty.Of("option", Ty.Val) | Ty.Val => coerce(coerce(r, Ty.Val), Ty.list(Ty.Val))
      case Ty.Of("option", of)              => coerce(r, of)
      case _                                => r

  /** A set of threads held in a variable: a list. */
  private def threads(c: Call, on: Term)(using Env): Option[Res] =
    if !isA(on, set) || !reprOf(on).contains(Ty.list(Ty.Tid)) then None
    else (c.name, c.args) match
      case ("contains", List(t)) => Some(applied("tset_contains", List(expr(on), coerce(expr(t), Ty.Tid)), Ty.Bool,
        Res.Kind.Value))
      case ("+", List(t))        => Some(applied("tset_add", List(expr(on), coerce(expr(t), Ty.Tid)), Ty.list(Ty.Tid),
        Res.Kind.Value))
      case _                     => None
