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

  /** The Scala variables in scope, each the term it is bound to (a method's `this` by its class); `kept`, the
    * values the compiler names a copy's unchanged fields by (`unchanged`), which are no values of the Scala as
    * written; and `reading`, the methods whose bodies are being read (`ReadMethods`).
    */
  final case class Env(bound: Map[Symbol, Expr[DTerm[?]]], kept: Set[Symbol], reading: Set[Symbol]):
    def contains(s: Symbol): Boolean = bound.contains(s)
    def apply(s: Symbol): Expr[DTerm[?]] = bound(s)
    def +(x: (Symbol, Expr[DTerm[?]])): Env = copy(bound = bound + x)
    def ++(xs: List[(Symbol, Expr[DTerm[?]])]): Env = copy(bound = bound ++ xs)
    def keeping(s: Symbol): Env = copy(kept = kept + s)
    def entering(method: Symbol): Env = copy(reading = reading + method)

  object Env:
    def of(xs: (Symbol, Expr[DTerm[?]])*): Env = Env(xs.toMap, Set.empty, Set.empty)

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

  /** Whether a type of the developer's (or a case of it) declares its own `equals`: its `==` is then not data's
    * structural equality, which is what the term's and Lean's equality are.
    */
  def ownEquals(t: TypeRepr): Boolean = t.classSymbol.toList.flatMap(c => c :: c.children).exists(c =>
    c.isClassDef && !List("scala.", "java.").exists(c.fullName.startsWith) &&
      c.declaredMethod("equals").exists(m => !m.flags.is(Flags.Synthetic)))

  /** A store: a class of Scala's `caps.Mutable`, whose state (its one `var`) its `update` methods change. */
  def isStore(t: TypeRepr): Boolean = t.baseClasses.exists(_.fullName == "scala.caps.Mutable")

  /** A port: a store, or a service, a class of the developer's that holds ports. In the Scala that changes one
    * (`steps.StepReader`) a port's variable stands for its state: the store's, or the states of the ports held.
    */
  def isPort(t: TypeRepr): Boolean = isStore(t) || held(t.typeSymbol).nonEmpty

  /** The fields of a class of the developer's that are ports, in order; none of a case class, which is data. */
  def held(c: Symbol): List[Symbol] =
    if !c.isClassDef || c.flags.is(Flags.Case) || List("scala.", "java.").exists(c.fullName.startsWith) then Nil
    else c.declaredFields.filter(f => isPort(c.typeRef.memberType(f)))

  /** A store's one `var`, where its state is; or the compile error of a store with none or several. */
  def storeVar(store: Symbol, at: Tree): Symbol = store.declaredFields.filter(_.flags.is(Flags.Mutable)) match
    case List(state) => state
    case found       => refuse(s"the store ${store.name}, whose state is not one `var` (it has ${found.size})", at)

  /** Where, in the state of the port `on`, the state its member `f` names is: the whole of it (`Some(None)`: a
    * store's `var`, the one port a service holds), a field of it (`Some(Some(name))`: one of several ports held);
    * `None` of a member that is no part of the state.
    */
  def partOf(on: TypeRepr, f: Symbol, at: Tree): Option[Option[String]] =
    if isStore(on) then Option.when(storeVar(on.typeSymbol, at) == f)(None)
    else held(on.typeSymbol) match
      case List(one) => Option.when(one == f)(None)
      case several   => Option(several.indexOf(f)).filter(_ >= 0).map(i => Some(fieldsOf(stateType(on, at))(i)._1))

  /** The type of a port's state: a store's `var`'s; of a service holding one port, that port's; of a service
    * holding several, the case class its companion names (`type State = …`), one field per port in order.
    */
  def stateType(port: TypeRepr, at: Tree): TypeRepr =
    if isStore(port) then port.memberType(storeVar(port.typeSymbol, at))
    else held(port.typeSymbol) match
      case List(one) => stateType(port.memberType(one), at)
      case several   => namedState(port, several.map(f => stateType(port.memberType(f), at)), at)

  private def namedState(port: TypeRepr, parts: List[TypeRepr], at: Tree): TypeRepr =
    val c = port.typeSymbol
    val alias = c.companionModule.moduleClass.typeMember("State")
    if alias.isNoSymbol then refuse(s"the service ${c.name}, which holds ${parts.size} ports and names no state: " +
      "say `type State = …` in its companion, a case class with one field per port, in order", at)
    val state = c.companionModule.termRef.select(alias).dealias
    val fields = fieldsOf(state).map(_._2)
    if fields.size != parts.size || !fields.zip(parts).forall(_ =:= _) then refuse(s"the service ${c.name}, whose " +
      s"state ${state.show} is not a case class of its ports' states in order (${parts.map(_.show).mkString(", ")})",
      at)
    state

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
