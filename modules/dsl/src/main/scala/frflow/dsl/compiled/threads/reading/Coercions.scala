package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term as Rocq, Ty}

/** A value read at one type, used at another.
  *
  *   - An object of a class of the unit held where a `val` is, is `VObj (O_C x)`; read back at its class it is cast
  *     (`cast_C`), a failed cast being `type_error`.
  *   - A value that may be null is an option: one that is not null is `Some`; where it must not be null it is
  *     `unnull`.
  *   - A case of a sum used as the sum is the case's constructor; a sum cast to a case (`asInstanceOf`) is
  *     `cast_<case>`.
  *   - A `Unit` where a `val` is wanted is `VUnit`.
  *   - A `val` read as a list is cast to a list of `val`s (`cast_list`): its elements are cast where they are read.
  */
private[threads] trait Coercions extends ReadSigs:

  def coerce(r: Res, to: Ty)(using Env): Res = coerced(r, to, value)

  /** `r` at `to`, each program on the way giving a value named `name`. */
  def coerceAs(r: Res, to: Ty, name: String)(using Env): Res = coerced(r, to, valueAs(_, name))

  private def isUnitType(name: String): Boolean = typeNames.values.exists(_ == name)

  private def coerced(r: Res, to: Ty, held: Res => Res)(using Env): Res =
    if fits(r.ty, to) then r.copy(ty = to, term = typed(r.term, to))
    else (r.ty, to) match
      case (Ty.Unit, Ty.Val) | (_, Ty.Unit)      => dropped(r, to)
      case (_, Ty.Val)                           => injected(held(r))
      case (Ty.Of("option", Ty.Val), Ty.Of("option", Ty.Named(c))) if isUnitType(c) =>
        through(catalogue.fromNullable(c), held(r), to)
      case (from, Ty.Of("option", of)) if !isOption(from) => some(held(coerced(r, of, held)), to)
      case (Ty.Of("option", of), _) if !isOption(to) => coerced(through("unnull", held(r), of), to, held)
      case (Ty.Val, Ty.Named(c)) if isUnitType(c) => through(catalogue.fromVal(c), held(r), to)
      case (Ty.Val, Ty.Of("list", _))            => through(catalogue.list, held(r), Ty.list(Ty.Val))
      case (Ty.Named(from), Ty.Named(c))         => between(held(r), from, c)
      case _                                     => refuse(s"a value of type ${r.ty} where one of $to is wanted")

  private def isOption(t: Ty): Boolean = t match
    case Ty.Of("option", _) => true
    case _                  => false

  /** Whether a value of `from` is one of `to` as it is: `Never` is of every type. */
  def fits(from: Ty, to: Ty): Boolean = (from, to) match
    case (Ty.Never, _)                  => true
    case (Ty.Of(c, a), Ty.Of(d, b))     => c == d && fits(a, b)
    case (Ty.Sum(a, b), Ty.Sum(c, d))   => fits(a, c) && fits(b, d)
    case (Ty.Prod(as), Ty.Prod(bs))     => as.size == bs.size && as.zip(bs).forall(fits(_, _))
    case _                              => from == to

  /** An empty list, or a null, given the type it is used at. */
  private def typed(t: Rocq, to: Ty): Rocq = (t, to) match
    case (Rocq.At(name, _), Ty.Of(_, of)) => Rocq.At(name, of)
    case _                                => t

  /** As the argument of a constructor, an operation or a definition, whose parameter gives its type: `None`, `[]`. */
  def bare(t: Rocq): Rocq = t match
    case Rocq.At("None", _) => Rocq.Ref("None")
    case Rocq.At("nil", _)  => Rocq.Items(Nil)
    case other              => other

  /** A constant applied to expressions read, each a value. */
  def applied(name: String, parts: List[Res], gives: Ty, kind: Res.Kind)(using Env): Res =
    val (steps, terms) = values(parts)
    Res(steps, Rocq.of(name, terms.map(bare)*), gives, kind)

  /** `r` run, what it gives dropped: `tt`, or `VUnit` where a `val` is wanted. */
  private def dropped(r: Res, to: Ty): Res =
    Res(r.steps ++ Option.when(!r.isValue)(Step.Bind("_", r.term)), if to == Ty.Val then Rocq.Ref("VUnit")
      else Rocq.unit, to, Res.Kind.Value)

  private def through(cast: String, v: Res, to: Ty): Res =
    Res(v.steps, Rocq.of(cast, bare(v.term)), to, Res.Kind.Program)

  private def some(v: Res, to: Ty): Res = Res(v.steps, Rocq.of("Some", bare(v.term)), to, Res.Kind.Value)

  private def injected(v: Res): Res =
    val term = (v.ty, v.term) match
      case (Ty.Named(c), _) if isUnitType(c)       => Rocq.of("VObj", Rocq.of(catalogue.obj(c), v.term))
      case (Ty.Bool, _)                            => Rocq.of("VBool", v.term)
      case (Ty.Tid, _)                             => Rocq.of("VTid", v.term)
      case (Ty.Exn, _)                             => Rocq.of("VExn", v.term)
      case (Ty.Code, _)                            => Rocq.of("VCode", v.term)
      case (Ty.Of("list", _), Rocq.At("nil", _))   => Rocq.of("VList", Rocq.Items(Nil))
      case _                                       => refuse(s"a value of type ${v.ty} held as a val")
    Res(v.steps, term, Ty.Val, Res.Kind.Value)

  /** A case of a sum as the sum, or a sum as one of its cases. */
  private def between(v: Res, from: String, to: String): Res =
    (caseHolding(from).filter(_._1.name == to), caseHolding(to).filter(_._1.name == from)) match
      case (Some((_, c)), _)   => Res(v.steps, Rocq.of(c.ctor, v.term), Ty.Named(to), Res.Kind.Value)
      case (_, Some((s, c)))   => through(catalogue.fromSum(s.name, to, c.ctor), v, Ty.Named(to))
      case _                   => refuse(s"a value of type $from where one of $to is wanted")
