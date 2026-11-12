package frflow.dsl.lifted.steps

import frflow.dsl.term.{DataMacros, LeanType}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** The ports a reading of Scala that changes one is over (`StepReader`). The code is read of one port, the root:
  * its variable is bound to the whole state. A service holding several ports has a state with a field for each, so
  * the state of a port it holds is a part of it; a call made on that port reads the part and leaves the whole
  * with the part replaced.
  */
private[steps] trait StepPorts:
  this: StepReader =>
  import r.q.reflect.*

  /** Where a port's state is: in the state the variable `key` is bound to, under `path` (fields of the states of
    * services holding several ports, outermost first).
    */
  final case class Place(key: Symbol, path: List[String])

  /** The ports of a reading: the variable bound to the whole state (`root`); for each other variable bound to a
    * port's state, where in another's that state is (`up`); and whether the reading is inside one step (an
    * `update` method's body, a reading of its own whose root is the store).
    */
  final case class Ports(root: Symbol, up: Map[Symbol, Place], atomic: Boolean):
    /** `key` and the variables its state is part of, innermost first, the root last. */
    def chain(key: Symbol): List[Symbol] = key :: up.get(key).fold(Nil)(above => chain(above.key))

  /** The port's class: `key` itself in a method's body, else the class of the variable `key` is. */
  def portOf(key: Symbol): Symbol = if key.isClassDef then key else key.termRef.widen.typeSymbol

  def stateOf(key: Symbol): TypeRepr = r.stateType(portOf(key).typeRef, Literal(UnitConstant()))

  private val nowhere: Tree = Literal(UnitConstant())

  /** Where a variable's state is looked into: a class that implements a service, whose constructor's fields its
    * state is made of; else the state's own type (a case class a service holding several ports names).
    */
  def whereOf(key: Symbol): TypeRepr =
    val port = portOf(key).typeRef
    if r.isImplementation(port) then port else stateOf(key)

  /** What is under a name where a state is looked into: the type it is declared with. */
  private def under(where: TypeRepr, name: String): TypeRepr =
    if r.isImplementation(where) then r.stateFieldType(where, name)
    else r.fieldsOf(where).find(_._1 == name).fold(r.refuse(s"the state's part $name", nowhere))(_._2)

  /** The selector of what is under a name, typed by the state it is a field of (`s`) and its own (`f`). */
  private def selector[S: Type, F: Type](where: TypeRepr, name: String)(using Quotes): Expr[LeanType.Field[S, F]] =
    if r.isImplementation(where) then r.stateField(where, name, nowhere).asExprOf[LeanType.Field[S, F]]
    else DataMacros.typedField[S, F](name, r.fieldsOf(where).indexWhere(_._1 == name))

  /** The type of the state at a place. */
  def stateAt(at: Place): TypeRepr = r.stateOfType(at.path.foldLeft(whereOf(at.key))(under), nowhere)

  /** The part of `state` under `path`, looked into as `where` says. */
  def part(state: Expr[DTerm[?]], where: TypeRepr, path: List[String])(using Quotes): Expr[DTerm[?]] = path match
    case Nil          => state
    case name :: rest =>
      val inner = under(where, name)
      (r.stateOfType(where, nowhere).asType, r.stateOfType(inner, nowhere).asType) match
        case ('[s], '[f]) => part('{ DTerm.select(${ state.asExprOf[DTerm[s]] },
          ${ selector[s, f](where, name) }) }, inner, rest)
        case _            => r.refuse(s"the state's part $name", nowhere)

  /** `state` with the part under `path` replaced by `by`. */
  def replaced(state: Expr[DTerm[?]], where: TypeRepr, path: List[String], by: Expr[DTerm[?]])(using Quotes)
      : Expr[DTerm[?]] = path match
    case Nil          => by
    case name :: rest =>
      val inner = under(where, name)
      (r.stateOfType(where, nowhere).asType, r.stateOfType(inner, nowhere).asType) match
        case ('[s], '[f]) =>
          val field = selector[s, f](where, name)
          val whole = state.asExprOf[DTerm[s]]
          '{ DTerm.copy($whole, $field.selector, ${ replaced('{ DTerm.select($whole, $field) }, inner, rest, by)
            .asExprOf[DTerm[f]] }) }
        case _            => r.refuse(s"the state's part $name", nowhere)

  /** Where the state of the port `on` names is: a variable's, `this`'s, or a field's of one of those. */
  def placeOf(on: Term)(using walk: Walk): Place = r.bare(on) match
    case self: This                                      => Place(self.tpe.typeSymbol, Nil)
    case id: Ident if walk.env.contains(id.symbol)       => Place(id.symbol, Nil)
    case id: Ident if walk.env.contains(id.symbol.owner) =>
      within(Place(id.symbol.owner, Nil), id.symbol.owner.typeRef, id)
    case field @ Select(holder, _)                       => within(placeOf(holder), holder.tpe.widen, field)
    case other                                           => unreached(other)

  private def within(holder: Place, of: TypeRepr, field: Term): Place =
    r.partOf(of, field.symbol, field).fold(unreached(field))(under => holder.copy(path = holder.path ++ under))

  private def unreached(on: Term): Nothing =
    r.refuse("a port reached this way: a port is a variable, `this`, or a field of one that holds it", on)

  /** The state at a place, as the reading has it. */
  def stateIn(at: Place)(using walk: Walk)(using Quotes): Expr[DTerm[?]] =
    part(walk.env(at.key), whereOf(at.key), at.path)

  /** The reading with `key`, and every variable between it and the root, bound to its part of the whole state:
    * what they are once the whole state is another (other calls left it, or a conditional's branch did).
    */
  def derived(key: Symbol)(using walk: Walk)(using Quotes): Walk =
    walk.ports.chain(key).reverse.drop(1).foldLeft(walk) { (w, k) =>
      val above = w.ports.up(k)
      w.bound(k, part(w.env(above.key), whereOf(above.key), above.path))
    }

  /** The reading once the state `key` is bound to is `state`: bound, and every state it is part of made again with
    * it, each named for what follows.
    */
  def put[Out: Type](key: Symbol, state: Expr[DTerm[?]])(rest: Walk => Quotes ?=> Expr[DTerm[Out]])(
      using walk: Walk)(using Quotes): Expr[DTerm[Out]] =
    val here = walk.bound(key, state)
    walk.ports.up.get(key).fold(rest(here))(above => putAt[Out](above, state)(rest)(using here))

  /** The reading once the state at a place is `state`. */
  def putAt[Out: Type](at: Place, state: Expr[DTerm[?]])(rest: Walk => Quotes ?=> Expr[DTerm[Out]])(
      using walk: Walk)(using Quotes): Expr[DTerm[Out]] =
    if at.path.isEmpty then put[Out](at.key, state)(rest)
    else
      val whole = stateOf(at.key)
      val made = replaced(walk.env(at.key), whereOf(at.key), at.path, state)
      named[Out](decapitalized(whole.typeSymbol.name), whole, made)(y => put[Out](at.key, y)(rest))
