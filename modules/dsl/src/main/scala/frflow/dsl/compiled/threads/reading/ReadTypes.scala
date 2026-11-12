package frflow.dsl.compiled.threads.reading

import frflow.core.threads.Ty
import frflow.dsl.compiled.threads.known.{Jdk, Thrown}

/** The type a Scala type's values are read at. A class of the unit is its type; a class of the JDK is what
  * `Jdk.types` says (a thread its id, an object with state a reference); a throwable is an `exn`; a class not read
  * is a handle; `Option`, `List` and `Either` are Rocq's; a `Set[Thread]` held in a variable is a list; a by-name
  * or function type is a closure (`code`); a type parameter, or a union, is a `val`. Any other type is not read.
  */
private[threads] trait ReadTypes extends Reading:
  import q.reflect.*

  /** The classes of the unit, each with the name of the type it is read as (`ReadShapes`). */
  def typeNames: Map[Symbol, String]

  def repr(t: TypeRepr): Ty = t match
    case ByNameType(_) => Ty.Code
    case _             => plain(t) match
      case OrType(_, _)                 => Ty.Val
      case AndType(l, r)                => List(l, r).map(repr).distinct match
        case List(one) => one
        case _         => refuse(s"a value of type ${t.show}")
      case f if isFunction(f)           => Ty.Code
      case AppliedType(c, args)         => applied(c.typeSymbol.fullName, args).getOrElse(ofClass(c.typeSymbol))
      case other                        => ofClass(other.typeSymbol)

  /** The type without its aliases, its annotations and its singletons. */
  def plain(t: TypeRepr): TypeRepr = t.widen.dealias match
    case AnnotatedType(under, _) => plain(under)
    case Refinement(under, _, _) => plain(under)
    case other                   => other

  def isFunction(t: TypeRepr): Boolean = t.isFunctionType || t.isContextFunctionType

  /** The type of a parameter: one of type `Nothing` takes a `val` (there is none to give it). */
  def reprOfParam(t: TypeRepr): Ty = repr(t) match
    case Ty.Never => Ty.Val
    case other    => other

  private def applied(cls: String, args: List[TypeRepr]): Option[Ty] = (cls, args) match
    case ("scala.Option" | "scala.Some", List(a))                        => Some(Ty.option(repr(a)))
    case ("scala.collection.immutable.List" | "scala.collection.immutable.::", List(a)) => Some(Ty.list(repr(a)))
    case ("scala.util.Either" | "scala.util.Left" | "scala.util.Right", List(a, b))     =>
      Some(Ty.Sum(repr(a), repr(b)))
    case ("scala.collection.immutable.Set", List(a)) if repr(a) == Ty.Tid => Some(Ty.list(Ty.Tid))
    case _                                                               => None

  /** The classes `sym` is, itself first. */
  def bases(sym: Symbol): List[Symbol] = if sym.isClassDef then sym.typeRef.baseClasses else Nil

  def isThrowable(sym: Symbol): Boolean = bases(sym).exists(_.fullName == Thrown.Throwable)
  def isOpaque(sym: Symbol): Boolean = bases(sym).exists(b => unit.opaque.contains(b.fullName))

  /** The class of the unit `sym` is read as, if it is one. */
  def unitType(sym: Symbol): Option[String] = bases(sym).collectFirst(Function.unlift(typeNames.get))

  private def ofClass(sym: Symbol): Ty =
    if sym.isTypeDef && !sym.isClassDef then Ty.Val
    else unitType(sym).map(Ty.Named(_))
      .orElse(bases(sym).collectFirst(Function.unlift(b => Jdk.types.get(b.fullName))))
      .orElse(Option.when(isThrowable(sym))(Ty.Exn)).orElse(Option.when(isOpaque(sym))(Ty.Nat))
      .getOrElse(refuse(s"a value of the class ${sym.fullName}"))

  /** What a concurrent set of the JDK holds, if `t` is one. */
  def setOf(t: TypeRepr): Option[Ty] =
    val set = Symbol.requiredClass(Jdk.SetClass)
    Option.when(bases(plain(t).typeSymbol).contains(set))(plain(t).baseType(set).typeArgs.map(repr))
      .flatMap(_.headOption)

  /** A name the compiler made, not the source. */
  def made(sym: Symbol): Boolean = sym.flags.is(Flags.Synthetic) || sym.name.contains("$")
