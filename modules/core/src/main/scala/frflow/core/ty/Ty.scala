package frflow.core.ty

import frflow.core.name.TypeName

/** The type of an expression: the standard types, the domain's (`Sort`, `Data`), the models' states (`World`), a
  * program's (`FlowOf`), and `Never`, the type of a step that only raises.
  */
enum Ty:
  case Bool, Str, Unit, World, Never
  case Num(kind: NumKind)
  case ListOf(elem: Ty)
  case OptionOf(elem: Ty)
  case EitherOf(error: Ty, value: Ty)
  case MapOf(key: Ty, value: Ty)
  case SetOf(elem: Ty)
  case TupleOf(elems: List[Ty])
  case FnOf(params: List[Ty], result: Ty)
  /** An opaque domain type (`Opaque("User", …)`): open until a definition fixes it. */
  case Sort(name: TypeName)
  /** A case class or an enum, declared in the vocabulary. */
  case Data(name: TypeName)
  /** A program: what a run that succeeds gives, and the error one may fail with (`Progs.failsWith`). */
  case FlowOf(result: Ty, error: Option[Ty])

object Ty:
  /** A function type applied to one argument: the rest of its inputs, or its result; a program applied to a world,
    * its run from it (as Lean types a program: `World → outcome × World`, `Defining.runs`). Applying anything else is
    * a FrFlow bug: the DSL applies functions only.
    */
  def applied(t: Ty): Ty = t match
    case FnOf(_ :: Nil, r)  => r
    case FnOf(_ :: rest, r) => FnOf(rest, r)
    case FlowOf(r, e)       => TupleOf(List(e.fold(r)(EitherOf(_, r)), World))
    case other              => throw IllegalStateException(s"FrFlow bug: a value of type $other applied")

  /** A function type's result; any other type is its own. */
  def resultOf(t: Ty): Ty = t match
    case FnOf(_, r) => r
    case other      => other

  /** What a value of `t` gives: a program's run that succeeds, its result; any other value, itself. */
  def yields(t: Ty): Ty = t match
    case FlowOf(r, _) => r
    case other        => other

  /** The error a program of type `t` (or a function giving one) may fail with. */
  def errorOf(t: Ty): Option[Ty] = resultOf(t) match
    case FlowOf(_, e) => e
    case _            => None

  /** A program type (or a function giving one) given the error its runs may fail with. */
  def failing(t: Ty, error: Option[Ty]): Ty = t match
    case FnOf(ps, r)  => FnOf(ps, failing(r, error))
    case FlowOf(r, _) => FlowOf(r, error)
    case other        => other

  /** The element type of a list, an option or a set. */
  def elementOf(t: Ty): Option[Ty] = t match
    case ListOf(a)   => Some(a)
    case OptionOf(a) => Some(a)
    case SetOf(a)    => Some(a)
    case _           => None

  /** The types `t` is made of, itself first. */
  def parts(t: Ty): List[Ty] = t :: (t match
    case ListOf(a)       => parts(a)
    case OptionOf(a)     => parts(a)
    case SetOf(a)        => parts(a)
    case FlowOf(a, e)    => parts(a) ++ e.toList.flatMap(parts)
    case EitherOf(e, a)  => parts(e) ++ parts(a)
    case MapOf(k, v)     => parts(k) ++ parts(v)
    case TupleOf(as)     => as.flatMap(parts)
    case FnOf(as, r)     => (as :+ r).flatMap(parts)
    case _               => Nil)

  /** The domain types `t` names, in the order met. */
  def names(t: Ty): List[TypeName] = parts(t).collect { case Sort(n) => n; case Data(n) => n }.distinct

  /** The type both branches of a conditional have: a branch that only raises (a value or a program) takes the
    * other's.
    */
  def join(a: Ty, b: Ty): Ty = (a, b) match
    case (Never, _) | (FlowOf(Never, _), FlowOf(_, _)) => b
    case (_, Never) | (FlowOf(_, _), FlowOf(Never, _)) => a
    case _ if a == b                                   => a
    case _ => throw IllegalStateException(s"FrFlow bug: branches of types $a and $b")
