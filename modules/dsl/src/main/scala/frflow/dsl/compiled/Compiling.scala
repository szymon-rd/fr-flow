package frflow.dsl.compiled

import cats.syntax.all.*
import frflow.dsl.lifted.{FrSpec, NotRead}
import frflow.dsl.structure.{ReadPorts, StructureDeclaration}
import frflow.dsl.term.{LeanType, Terms}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** What the compiler knows of structures while it reads one class: the record that class's state is, by its
  * structure's name (`records`); for each field that holds a structure, the word given for it (`wiring`); the
  * traits in play that are no `caps.Mutable` (`traits`); and the class loader the class came from, where its
  * types' specs are found (`Specs`).
  */
final case class Known(records: Map[String, FrSpec[Any]], wiring: Map[String, StructureDeclaration[?]],
    traits: Set[String], loader: ClassLoader)

/** What every part of the compiler shares (`Compiler`): the tree of a compiled class as its TASTy has it (`q`),
  * and the terms it is read into, built as they are read. Each Scala construct read is one operation of the term
  * language; any other is refused with its place (`NotRead`).
  */
private[compiled] trait Compiling extends ReadPorts:
  import q.reflect.*
  given Quotes = q

  def known: Known
  val once: Once = Once()
  def inPlay: Set[String] = known.traits

  /** The Scala variables in scope, each the term it is bound to (a method's `this` by its class); `kept`, the
    * values the compiler names a copy's unchanged fields by; and `reading`, the methods whose bodies are being
    * read.
    */
  final case class Env(bound: Map[Symbol, DTerm[Any]], kept: Set[Symbol], reading: Set[Symbol]):
    def contains(s: Symbol): Boolean = bound.contains(s)
    def apply(s: Symbol): DTerm[Any] = bound(s)
    def +(x: (Symbol, DTerm[Any])): Env = copy(bound = bound + x)
    def ++(xs: List[(Symbol, DTerm[Any])]): Env = copy(bound = bound ++ xs)
    def keeping(s: Symbol): Env = copy(kept = kept + s)
    def entering(method: Symbol): Env = copy(reading = reading + method)

  object Env:
    def of(xs: (Symbol, DTerm[Any])*): Env = Env(xs.toMap, Set.empty, Set.empty)

  /** A method applied: its receiver, its name, its arguments (every list's, in order), and the whole call. */
  final case class Calling(on: Term, name: String, args: List[Term], whole: Term):
    def own: TypeRepr = whole.tpe.widen

  /** `t` as a term of `as`, the type its value is used at. */
  def read(t: Term, as: TypeRepr)(using Env): DTerm[Any]

  /** The spec of a type a value of the Scala has, or the refusal naming it: a structure's, the record of the
    * class being read that implements it, else its name alone; a standard type's; a type of the developer's, the
    * one its companion gives.
    */
  def spec(t: TypeRepr, at: Tree): FrSpec[Any] = specOf(t).getOrElse(refuse(s"a value of type ${t.show}, " +
    "which has no FrSpec: derive one (`derives FrSpec`) or give one in its companion; Scala's Int and Long " +
    "have none (use BigInt)", at))

  /** A domain type is one with a spec. */
  override def isDomain(t: TypeRepr): Boolean = specOf(t).nonEmpty

  private def specOf(t: TypeRepr): Option[FrSpec[Any]] =
    def of(part: TypeRepr): Option[FrSpec[Any]] = specOf(part)
    def standard: Option[FrSpec[?]] = t.dealias match
      case s if s =:= TypeRepr.of[Boolean]                         => Some(FrSpec[Boolean])
      case s if s =:= TypeRepr.of[BigInt]                          => Some(FrSpec[BigInt])
      case s if s =:= TypeRepr.of[String]                          => Some(FrSpec[String])
      case s if s =:= TypeRepr.of[Unit]                            => Some(FrSpec[Unit])
      case AppliedType(c, List(a, b)) if c.typeSymbol == PairClass => (of(a), of(b)).tupled.map(FrSpec.pair[Any])
      case AppliedType(c, List(a)) if c.typeSymbol == ListClass    => of(a).map(FrSpec.list[Any])
      case AppliedType(c, List(a)) if c.typeSymbol == OptionClass  => of(a).map(FrSpec.option[Any])
      case AppliedType(c, List(a)) if c.typeSymbol == SetClass     => of(a).map(FrSpec.set[Any])
      case AppliedType(c, List(k, v)) if c.typeSymbol == MapClass  => (of(k), of(v)).tupled.map(FrSpec.map[Any])
      case _                                                       => None
    structureOf(t).map(s => known.records.getOrElse(s.fullName, FrSpec.named[Any](s.name))).orElse(standard)
      .orElse(Specs.given_(known.loader, t.typeSymbol.fullName)).map(_.asInstanceOf[FrSpec[Any]])

  /** The refusal of Scala the compiler does not read, with its place. */
  def refuse(what: String, at: Tree): Nothing =
    NotRead.raise(using q)(s"FrFlow: lifted code cannot hold $what", Some(at))

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

  /** Whether `t` names the object of the type `module` (`List`, `Some`, `Nil`), however it is reached. */
  def names(t: Term, module: TypeRepr): Boolean =
    t.tpe.typeSymbol != defn.NothingClass && t.tpe.typeSymbol == module.typeSymbol

  /** An enum's case without fields, named (`Shape.Empty`). */
  def isEnumValue(t: Term): Boolean =
    val s = t.symbol
    !s.isNoSymbol && s.isTerm && s.flags.is(Flags.Enum) && s.flags.is(Flags.Case) && !s.flags.is(Flags.Module) &&
      !s.flags.is(Flags.Method)

  /** A field a copy leaves as it is: the compiler's default for it, or the value the compiler named it by. */
  def unchanged(arg: Term)(using env: Env): Boolean =
    val s = bare(arg).symbol
    !s.isNoSymbol && (s.name.startsWith("copy$default$") || env.kept(s))

  /** Whether a type of the developer's (or a case of it) declares its own `equals`. */
  def ownEquals(t: TypeRepr): Boolean = t.classSymbol.toList.flatMap(c => c :: c.children).exists(c =>
    c.isClassDef && !List("scala.", "java.").exists(c.fullName.startsWith) &&
      c.declaredMethod("equals").exists(m => !m.flags.is(Flags.Synthetic)))

  /** A function given to an operation as a function of its input's term: a lambda written out, its parameter
    * bound to the term, its body read as a `b`.
    */
  def function(f: Term, b: TypeRepr)(using env: Env): DTerm[Any] => DTerm[Any] = bare(f) match
    case Lambda(List(p), body) =>
      val made = once(List(input(p)))(xs => read(body, b)(using env + ((p.symbol, xs.head))))
      x => made(List(x))
    case other                 => refuse("a function that is not a lambda written out", other)

  def function2(f: Term, r: TypeRepr)(using env: Env): (DTerm[Any], DTerm[Any]) => DTerm[Any] = bare(f) match
    case Lambda(List(a, b), body) =>
      val made = once(List(input(a), input(b)))(xs =>
        read(body, r)(using env + ((a.symbol, xs(0))) + ((b.symbol, xs(1)))))
      (x, y) => made(List(x, y))
    case other                    => refuse("a function of two inputs that is not a lambda written out", other)

  private def input(p: ValDef): (String, LeanType[Any]) = (p.name, spec(p.tpt.tpe, p))

  /** A value named for what follows it (Lean's `let`), what follows compiled now (`Once`). */
  def bind(value: DTerm[Any], name: String)(rest: DTerm[Any] => DTerm[Any])(using out: LeanType[Any]): DTerm[Any] =
    val made = once(List((name, value.leanType)))(xs => rest(xs.head))
    Terms.let[Any, Any](value, name, x => made(List(x)))

  /** The names a lambda gives its parameters, for printing. */
  def hints(f: Term): List[String] = bare(f) match
    case Lambda(ps, _) => ps.map(_.name)
    case _             => List("x", "y")
