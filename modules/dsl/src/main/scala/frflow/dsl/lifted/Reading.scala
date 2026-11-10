package frflow.dsl.lifted

import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** What every part of the reader shares (`Reader`): the Scala is read with the compiler's view where the code is
  * lifted (`q`); a term is written with the quotes of the place it is written in (each method's own `Quotes`), so
  * every binder the reader writes owns its body.
  */
private[lifted] trait Reading:
  val q: Quotes
  import q.reflect.*

  /** The Scala variables in scope, each the term it is bound to; and `kept`, the values the compiler names a
    * copy's unchanged fields by (`unchanged`), which are no values of the Scala as written.
    */
  final case class Env(bound: Map[Symbol, Expr[DTerm[?]]], kept: Set[Symbol]):
    def contains(s: Symbol): Boolean = bound.contains(s)
    def apply(s: Symbol): Expr[DTerm[?]] = bound(s)
    def +(x: (Symbol, Expr[DTerm[?]])): Env = copy(bound = bound + x)
    def ++(xs: List[(Symbol, Expr[DTerm[?]])]): Env = copy(bound = bound ++ xs)
    def keeping(s: Symbol): Env = copy(kept = kept + s)

  object Env:
    def of(xs: (Symbol, Expr[DTerm[?]])*): Env = Env(xs.toMap, Set.empty)

  /** A method applied: its receiver, its name, its arguments (every list's, in order), and the whole call. */
  final case class Calling(on: Term, name: String, args: List[Term], whole: Term):
    def own: TypeRepr = whole.tpe.widen

  /** `t` as a term of `as`, the type its value is used at. */
  def read(t: Term, as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]]

  def readAs[A: Type](t: Term)(using Env)(using Quotes): Expr[DTerm[A]] =
    read(t, TypeRepr.of[A]).asExprOf[DTerm[A]]

  /** The spec of a type a value of the Scala has, or the compile error naming it. */
  def spec[A: Type](at: Tree)(using Quotes): Expr[FrSpec[A]] =
    Expr.summon[FrSpec[A]].getOrElse(refuse(s"a value of type ${Type.show[A]}, which has no FrSpec: derive one " +
      "(`derives FrSpec`) or give one in its companion; Scala's Int and Long have none (use BigInt)", at))

  /** The compile error for Scala the reader does not read, at the Scala. */
  def refuse(what: String, at: Tree): Nothing =
    report.errorAndAbort(s"FrFlow: lifted code cannot hold $what", at.pos)

  /** `t` under what the compiler wraps an expression in: an inlining with no bindings, an ascription, a block of
    * nothing.
    */
  def bare(t: Term): Term = t match
    case Inlined(_, Nil, b) => bare(b)
    case Typed(b, _)        => bare(b)
    case Block(Nil, b)      => bare(b)
    case other              => other

  /** A method selected and applied, whatever its type arguments and argument lists. */
  object Call:
    def unapply(t: Term): Option[(Term, String, List[Term])] = t match
      case Apply(f, args)   => unapply(f).map((on, name, before) => (on, name, before ++ args))
      case TypeApply(f, _)  => unapply(f)
      case Select(on, name) => Some((on, name, Nil))
      case _                => None

  val ListClass: Symbol = Symbol.requiredClass("scala.collection.immutable.List")
  val OptionClass: Symbol = Symbol.requiredClass("scala.Option")
  val SetClass: Symbol = Symbol.requiredClass("scala.collection.immutable.Set")
  val MapClass: Symbol = Symbol.requiredClass("scala.collection.immutable.Map")
  val PairClass: Symbol = Symbol.requiredClass("scala.Tuple2")
  val SomeObject: Symbol = Symbol.requiredModule("scala.Some").moduleClass

  /** The type arguments `t` has as a `cls` (a list's element, a map's key and value); none if it is not one. */
  def argsOf(t: TypeRepr, cls: Symbol): List[TypeRepr] = t.widen.baseType(cls) match
    case AppliedType(_, args) => args
    case _                    => Nil

  def elementOf(t: TypeRepr, cls: Symbol): Option[TypeRepr] = argsOf(t, cls).headOption

  /** Whether `t` names the object `M` (`List`, `Some`, `Nil`), however it is reached. */
  def names[M: Type](t: Term): Boolean =
    t.tpe.typeSymbol != defn.NothingClass && t.tpe.typeSymbol == TypeRepr.of[M].typeSymbol

  /** An enum's case without fields, named (`Shape.Empty`). */
  def isEnumValue(t: Term): Boolean =
    val s = t.symbol
    !s.isNoSymbol && s.isTerm && s.flags.is(Flags.Enum) && s.flags.is(Flags.Case) && !s.flags.is(Flags.Module) &&
      !s.flags.is(Flags.Method)

  /** A field a copy leaves as it is: the compiler's default for it (`b.copy$default$1`), or the value the compiler
    * named it by when the copy's fields are given by name (`Env.kept`).
    */
  def unchanged(arg: Term)(using env: Env): Boolean =
    val s = bare(arg).symbol
    !s.isNoSymbol && (s.name.startsWith("copy$default$") || env.kept(s))

  /** A case class's fields, by name and type, in order. */
  def fieldsOf(t: TypeRepr): List[(String, TypeRepr)] = t.typeSymbol.caseFields.map(f => f.name -> t.memberType(f))

  /** A function given to an operation as a function of its input's term: a lambda written out, its parameter
    * bound to the term; or a lifted function named, called.
    */
  def function[A: Type, B: Type](f: Term)(using env: Env)(using Quotes): Expr[DTerm[A] => DTerm[B]] = bare(f) match
    case Lambda(List(p), body) => '{ (x: DTerm[A]) => ${ readAs[B](body)(using env + ((p.symbol, 'x))) } }
    case g if g.tpe <:< TypeRepr.of[Lifted.Of1[A, B]] =>
      '{ (x: DTerm[A]) => Defined.apply[A, B](${ g.asExprOf[Lifted.Of1[A, B]] })(x)(using ${ spec[B](f) }) }
    case other                 => refuse("a function that is neither a lambda written out nor a lifted one", other)

  def function2[A: Type, B: Type, R: Type](f: Term)(using env: Env)(using Quotes)
      : Expr[(DTerm[A], DTerm[B]) => DTerm[R]] = bare(f) match
    case Lambda(List(a, b), body) =>
      '{ (x: DTerm[A], y: DTerm[B]) => ${ readAs[R](body)(using env + ((a.symbol, 'x)) + ((b.symbol, 'y))) } }
    case other                    => refuse("a function of two inputs that is not a lambda written out", other)

  /** The names a lambda gives its parameters, for printing; `x` of a function named. */
  def hints(f: Term): List[String] = bare(f) match
    case Lambda(ps, _) => ps.map(_.name)
    case _             => List("x", "y")
