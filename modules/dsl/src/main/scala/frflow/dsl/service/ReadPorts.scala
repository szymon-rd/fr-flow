package frflow.dsl.service

import frflow.dsl.term.LeanType
import scala.quoted.*

/** What the reader of lifted code knows of ports (`lifted.Reading`): which types are services, classes that
  * implement one, stores, and classes holding ports; and the state each stands for where the Scala that changes
  * it is read (`lifted.steps.StepReader`).
  */
trait ReadPorts:
  val q: Quotes
  /** What the reading knows of services: the record of the class being read, the Definitions it is given. */
  def services: Services
  import q.reflect.*

  /** The compile error for Scala the reader does not read, at the Scala. */
  def refuse(what: String, at: Tree): Nothing

  private def own(s: Symbol): Boolean = !List("scala.", "java.").exists(s.fullName.startsWith)
  private def mutable(t: TypeRepr): Boolean = t.baseClasses.exists(_.fullName == "scala.caps.Mutable")

  /** The service a type is or implements: the trait of the developer's, one of Scala's `caps.Mutable`, that it is
    * or extends. A service is known by its members; a class that implements one is read (`steps.ServiceLift`).
    */
  def serviceOf(t: TypeRepr): Option[Symbol] =
    t.baseClasses.find(c => c.isClassDef && c.flags.is(Flags.Trait) && own(c) && mutable(c.typeRef))
  def isService(t: TypeRepr): Boolean = serviceOf(t).contains(t.typeSymbol)
  def isImplementation(t: TypeRepr): Boolean = serviceOf(t).exists(_ != t.typeSymbol)

  /** The fields an implementation's state is made of: its constructor's parameters, in order. */
  def stateFields(c: Symbol): List[Symbol] =
    c.primaryConstructor.paramSymss.flatten.filter(_.isTerm).map(p => c.fieldMember(p.name))

  /** A store: a class of Scala's `caps.Mutable` whose state is data: its one `var`, or, of a class that
    * implements a service, its constructor's fields, none of them a service.
    */
  def isStore(t: TypeRepr): Boolean = mutable(t) && !isService(t) &&
    (!isImplementation(t) || stateFields(t.typeSymbol).forall(f => serviceOf(t.memberType(f)).isEmpty))

  /** A port: a store, a service, or a class of the developer's that holds ports. In the Scala that changes one
    * (`steps.StepReader`) a port's variable stands for its state.
    */
  def isPort(t: TypeRepr): Boolean = isStore(t) || serviceOf(t).nonEmpty || held(t.typeSymbol).nonEmpty

  /** The fields of a class of the developer's that are ports, in order; none of a case class, which is data, or
    * of a class that implements a service, whose fields are its state.
    */
  def held(c: Symbol): List[Symbol] =
    if !c.isClassDef || c.flags.is(Flags.Case) || !own(c) || serviceOf(c.typeRef).nonEmpty then Nil
    else c.declaredFields.filter(f => isPort(c.typeRef.memberType(f)))

  /** A store's one `var`, where its state is; or the compile error of a store with none or several. */
  def storeVar(store: Symbol, at: Tree): Symbol = store.declaredFields.filter(_.flags.is(Flags.Mutable)) match
    case List(state) => state
    case found       => refuse(s"the store ${store.name}, whose state is not one `var` (it has ${found.size})", at)

  /** Where, in the state of the port `on`, the state its member `f` names is: the whole of it (`Some(None)`: a
    * store's `var`, the one port a service holds), a field of it (`Some(Some(name))`: one of several ports held,
    * a field of a class that implements a service); `None` of a member that is no part of the state.
    */
  def partOf(on: TypeRepr, f: Symbol, at: Tree): Option[Option[String]] =
    if isService(on) then None
    else if isImplementation(on) then
      Option.when(f.owner == on.typeSymbol && stateFields(on.typeSymbol).exists(_.name == f.name))(Some(f.name))
    else if isStore(on) then Option.when(storeVar(on.typeSymbol, at) == f)(None)
    else held(on.typeSymbol) match
      case List(one) => Option.when(one == f)(None)
      case several   => Option(several.indexOf(f)).filter(_ >= 0).map(i => Some(fieldsOf(stateType(on, at))(i)._1))

  /** The type of a port's state: a service's, the service's own type (a record named as its trait, its fields
    * those of the class that implements it); a store's `var`'s; of a class holding one port, that port's; of a
    * class holding several, the case class its companion names (`type State = …`), one field per port in order.
    */
  def stateType(port: TypeRepr, at: Tree): TypeRepr = serviceOf(port).map(_.typeRef).getOrElse(
    if isStore(port) then port.memberType(storeVar(port.typeSymbol, at))
    else held(port.typeSymbol) match
      case List(one) => stateType(port.memberType(one), at)
      case several   => namedState(port, several.map(f => stateType(port.memberType(f), at)), at))

  /** The state a type stands for where a state is read: a port's, its state's; a datum's, itself. */
  def stateOfType(t: TypeRepr, at: Tree): TypeRepr = if isPort(t) then stateType(t, at) else t

  /** A field of the state of a class that implements a service: the type it is declared with. */
  def stateFieldType(implementation: TypeRepr, name: String): TypeRepr =
    implementation.memberType(implementation.typeSymbol.fieldMember(name))

  /** The same field's selector, read off the record the implementation's state is (`services.records`). */
  def stateField(implementation: TypeRepr, name: String, at: Tree)(using Quotes): Expr[Any] =
    val service = serviceOf(implementation).get
    val record = services.records.getOrElse(service.fullName, refuse(s"the state of ${implementation.show}, " +
      "a class that implements a service, read where FrFlow is not reading that class (`lifted(…)`)", at))
    val i = stateFields(implementation.typeSymbol).indexWhere(_.name == name)
    (service.typeRef.asType, stateOfType(stateFieldType(implementation, name), at).asType) match
      case ('[s], '[f]) => '{ ${ record.asExprOf[LeanType[s]] }.fields(${ Expr(i) })
        .asInstanceOf[LeanType.Field[s, f]] }
      case _            => refuse(s"the field $name", at)

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
