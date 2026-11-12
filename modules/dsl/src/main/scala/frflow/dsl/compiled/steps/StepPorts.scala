package frflow.dsl.compiled.steps

import frflow.dsl.term.Term as DTerm

/** The ports a reading of Scala that changes one is over (`Steps`). The code is read of one port, the root: its
  * variable is bound to the whole state. The state of a port it holds is a part of that state; a call made on
  * that port reads the part and leaves the whole with the part replaced.
  */
private[steps] trait StepPorts:
  this: Steps =>
  import c.q.reflect.*

  /** Where a port's state is: in the state the variable `key` is bound to, under `path` (fields, outermost
    * first).
    */
  final case class Place(key: Symbol, path: List[String])

  /** The ports of a reading: the variable bound to the whole state (`root`); for each other variable bound to a
    * port's state, where in another's that state is (`up`); and whether the reading is inside one step.
    */
  final case class Ports(root: Symbol, up: Map[Symbol, Place], atomic: Boolean):
    /** `key` and the variables its state is part of, innermost first, the root last. */
    def chain(key: Symbol): List[Symbol] = key :: up.get(key).fold(Nil)(above => chain(above.key))

  /** The port's class: `key` itself in a method's body, else the class of the variable `key` is. */
  def portOf(key: Symbol): Symbol = if key.isClassDef then key else key.termRef.widen.typeSymbol

  /** The part of `state` under `path`: each name a field of the record above it. */
  def part(state: DTerm[Any], path: List[String]): DTerm[Any] =
    path.foldLeft(state)((s, name) => s.selectDynamic(name).asInstanceOf[DTerm[Any]])

  /** `state` with the part under `path` replaced by `by`. */
  def replaced(state: DTerm[Any], path: List[String], by: DTerm[Any]): DTerm[Any] = path match
    case Nil          => by
    case name :: rest =>
      val field = state.leanType.fields.find(_.selector.name == name).getOrElse(
        c.refuse(s"the state's part $name", Literal(UnitConstant())))
      DTerm.copy(state, field.selector.asInstanceOf[frflow.core.term.Selector[Any, Any]],
        replaced(part(state, List(name)), rest, by))

  /** Where the state of the port `on` names is: a variable's, `this`'s, or a field's of one of those. */
  def placeOf(on: Term)(using walk: Walk): Place = c.bare(on) match
    case self: This                                      => Place(self.tpe.typeSymbol, Nil)
    case id: Ident if walk.env.contains(id.symbol)       => Place(id.symbol, Nil)
    case id: Ident if walk.env.contains(id.symbol.owner) =>
      within(Place(id.symbol.owner, Nil), id.symbol.owner.typeRef, id)
    case field @ Select(holder, _)                       => within(placeOf(holder), holder.tpe.widen, field)
    case other                                           => unreached(other)

  private def within(holder: Place, of: TypeRepr, field: Term): Place =
    c.partOf(of, field.symbol, field).fold(unreached(field))(under => holder.copy(path = holder.path ++ under))

  private def unreached(on: Term): Nothing =
    c.refuse("a port reached this way: a port is a variable, `this`, or a field of one that holds it", on)

  /** The state at a place, as the reading has it. */
  def stateIn(at: Place)(using walk: Walk): DTerm[Any] = part(walk.env(at.key), at.path)

  /** The reading with `key`, and every variable between it and the root, bound to its part of the whole state:
    * what they are once the whole state is another.
    */
  def derived(key: Symbol)(using walk: Walk): Walk =
    walk.ports.chain(key).reverse.drop(1).foldLeft(walk) { (w, k) =>
      val above = w.ports.up(k)
      w.bound(k, part(w.env(above.key), above.path))
    }

  /** The reading once the state `key` is bound to is `state`: bound, and every state it is part of made again
    * with it, each named for what follows.
    */
  def put(key: Symbol, state: DTerm[Any])(rest: Walk => DTerm[Any])(using walk: Walk): DTerm[Any] =
    val here = walk.bound(key, state)
    walk.ports.up.get(key).fold(rest(here))(above => putAt(above, state)(rest)(using here))

  /** The reading once the state at a place is `state`. */
  def putAt(at: Place, state: DTerm[Any])(rest: Walk => DTerm[Any])(using walk: Walk): DTerm[Any] =
    if at.path.isEmpty then put(at.key, state)(rest)
    else
      val whole = c.stateType(portOf(at.key).typeRef, Literal(UnitConstant()))
      named(decapitalized(whole.typeSymbol.name), replaced(walk.env(at.key), at.path, state))(y =>
        put(at.key, y)(rest))

  def decapitalized(name: String): String = name.take(1).toLowerCase + name.drop(1)
