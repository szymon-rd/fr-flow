package frflow.dsl.structure

import scala.quoted.*

/** What the class compiler knows of ports (`compiled.Compiling`): which types are structures, classes that
  * implement one, stores, and classes holding ports; and the state each stands for where the Scala that changes
  * it is read (`compiled.steps.Steps`).
  */
trait ReadPorts:
  val q: Quotes
  /** The traits this reading has as structures though they are no `caps.Mutable`, by name: the one the class
    * read implements, and those of the structures it holds.
    */
  def inPlay: Set[String]
  import q.reflect.*

  /** The compile error for Scala the reader does not read, at the Scala. */
  def refuse(what: String, at: Tree): Nothing

  private def own(s: Symbol): Boolean = !List("scala.", "java.").exists(s.fullName.startsWith)
  private def mutable(t: TypeRepr): Boolean = t.baseClasses.exists(_.fullName == "scala.caps.Mutable")

  /** The structure a type is or implements: the trait of the developer's that it is or extends, one of Scala's
    * `caps.Mutable` or one this reading has in play (`inPlay`). A structure is known by its members; a
    * class that implements one is compiled (`compiled.steps.ClassCode`).
    */
  def structureOf(t: TypeRepr): Option[Symbol] = t.baseClasses.find(c =>
    c.isClassDef && c.flags.is(Flags.Trait) && own(c) && (mutable(c.typeRef) || inPlay(c.fullName)))
  /** The same as a Declaration takes a trait for one (`StructureMacros.isStructure`), in play or not. */
  def declarableOf(t: TypeRepr): Option[Symbol] =
    t.baseClasses.find(c => StructureMacros.structured(using q)(c.typeRef, isDomain))
  /** Whether a type is a domain type, one with a `RocqType`: asked of the compiler, inside a compilation. */
  def isDomain(t: TypeRepr): Boolean =
    given Quotes = q
    t.asType match
      case '[x] => Expr.summon[frflow.dsl.term.RocqType[x]].nonEmpty
  def isStructure(t: TypeRepr): Boolean = structureOf(t).contains(t.typeSymbol)
  def isImplementation(t: TypeRepr): Boolean = structureOf(t).exists(_ != t.typeSymbol)

  /** The fields an implementation's state is made of: its constructor's parameters, in order. */
  def stateFields(c: Symbol): List[Symbol] =
    c.primaryConstructor.paramSymss.flatten.filter(_.isTerm).map(p => c.fieldMember(p.name))

  /** A store: a class of Scala's `caps.Mutable` whose state is data: its one `var`, or, of a class that
    * implements a structure, its constructor's fields, none of them a structure.
    */
  def isStore(t: TypeRepr): Boolean = !isStructure(t) && (
    if isImplementation(t) then stateFields(t.typeSymbol).forall(f => structureOf(t.memberType(f)).isEmpty)
    else mutable(t))

  /** A port: a store, a structure, or a class of the developer's that holds ports. In the Scala that changes one
    * (`steps.StepReader`) a port's variable stands for its state.
    */
  def isPort(t: TypeRepr): Boolean = isStore(t) || structureOf(t).nonEmpty || held(t.typeSymbol).nonEmpty

  /** The fields of a class of the developer's that are ports, in order; none of a case class, which is data, or
    * of a class that implements a structure, whose fields are its state.
    */
  def held(c: Symbol): List[Symbol] =
    if !c.isClassDef || c.flags.is(Flags.Case) || !own(c) || structureOf(c.typeRef).nonEmpty then Nil
    else c.declaredFields.filter(f => isPort(c.typeRef.memberType(f)))

  /** A store's one `var`, where its state is; or the compile error of a store with none or several. */
  def storeVar(store: Symbol, at: Tree): Symbol = store.declaredFields.filter(_.flags.is(Flags.Mutable)) match
    case List(state) => state
    case found       => refuse(s"the store ${store.name}, whose state is not one `var` (it has ${found.size})", at)

  /** Where, in the state of the port `on`, the state its member `f` names is: the whole of it (`Some(None)`: a
    * store's `var`, the one port a structure holds), a field of it (`Some(Some(name))`: one of several ports held,
    * a field of a class that implements a structure); `None` of a member that is no part of the state.
    */
  def partOf(on: TypeRepr, f: Symbol, at: Tree): Option[Option[String]] =
    if isStructure(on) then None
    else if isImplementation(on) then
      Option.when(f.owner == on.typeSymbol && stateFields(on.typeSymbol).exists(_.name == f.name))(Some(f.name))
    else if isStore(on) then Option.when(storeVar(on.typeSymbol, at) == f)(None)
    else held(on.typeSymbol) match
      case List(one) => Option.when(one == f)(None)
      case several   => Option(several.indexOf(f)).filter(_ >= 0).map(i => Some(fieldsOf(stateType(on, at))(i)._1))

  /** The type of a port's state: a structure's, the structure's own type (a record named as its trait, its fields
    * those of the class that implements it); a store's `var`'s; of a class holding one port, that port's; of a
    * class holding several, the case class its companion names (`type State = …`), one field per port in order.
    */
  def stateType(port: TypeRepr, at: Tree): TypeRepr = structureOf(port).map(_.typeRef).getOrElse(
    if isStore(port) then port.memberType(storeVar(port.typeSymbol, at))
    else held(port.typeSymbol) match
      case List(one) => stateType(port.memberType(one), at)
      case several   => namedState(port, several.map(f => stateType(port.memberType(f), at)), at))

  /** The state a type stands for where a state is read: a port's, its state's; a datum's, itself. */
  def stateOfType(t: TypeRepr, at: Tree): TypeRepr = if isPort(t) then stateType(t, at) else t

  /** A field of the state of a class that implements a structure: the type it is declared with. */
  def stateFieldType(implementation: TypeRepr, name: String): TypeRepr =
    implementation.memberType(implementation.typeSymbol.fieldMember(name))

  private def namedState(port: TypeRepr, parts: List[TypeRepr], at: Tree): TypeRepr =
    val c = port.typeSymbol
    val alias = c.companionModule.moduleClass.typeMember("State")
    if alias.isNoSymbol then refuse(s"the class ${c.name}, which holds ${parts.size} ports and names no state: " +
      "say `type State = …` in its companion, a case class with one field per port, in order", at)
    val state = c.companionModule.termRef.select(alias).dealias
    val fields = fieldsOf(state).map(_._2)
    if fields.size != parts.size || !fields.zip(parts).forall(_ =:= _) then refuse(s"the class ${c.name}, whose " +
      s"state ${state.show} is not a case class of its ports' states in order (${parts.map(_.show).mkString(", ")})",
      at)
    state

  /** A case class's fields, by name and type, in order. */
  def fieldsOf(t: TypeRepr): List[(String, TypeRepr)] = t.typeSymbol.caseFields.map(f => f.name -> t.memberType(f))
