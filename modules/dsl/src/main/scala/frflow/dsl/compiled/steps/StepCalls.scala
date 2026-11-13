package frflow.dsl.compiled.steps

import frflow.dsl.lifted.steps.Among
import frflow.dsl.structure.Call as MemberCall
import frflow.dsl.term.RocqType
import frflow.dsl.term.Term as DTerm

/** The calls a reading of Scala that changes a port follows (`Steps`): of a held structure's member (one step:
  * among other calls, they may have changed the state before it), of another of the class's own members (its body,
  * read where it is called), and what is carried from one step to the next.
  */
private[steps] trait StepCalls:
  this: Steps =>
  import c.q.reflect.*

  def isUpdate(m: Symbol): Boolean = m.isDefDef && m.flags.is(Flags.Mutable)

  /** Whether `t` needs no step: read alone or inside one step, it changes no port; among others, it uses none. */
  def quiet(t: Term)(using walk: Walk): Boolean = if walk.interleaved then !uses(t, false) else !uses(t, true)

  /** Whether `t` uses a port (`changing`: changes one): directly, or through a method of the developer's. */
  private def uses(t: Term, changing: Boolean, within: Set[Symbol] = Set.empty): Boolean =
    val found = new TreeAccumulator[Boolean]:
      def foldTree(seen: Boolean, tree: Tree)(owner: Symbol): Boolean = seen || (tree match
        case Assign(_, _)                                        => true
        case a: Apply if isUpdate(a.symbol) || through(a.symbol) => true
        case Select(on, _) if !changing && asked(on)             => true
        case s: Select if through(s.symbol)                      => true
        case other                                               => foldOverTree(seen, other)(owner))
      def through(m: Symbol): Boolean =
        !within(m) && c.isOwn(m) && c.kept(m).exists(d => uses(d.rhs.get, changing, within + m))
    found.foldTree(false, t)(Symbol.spliceOwner)

  /** A call of a port's method, or a read of its state: one step. */
  def storeCall(t: Term): Boolean = receiver(t).exists(asked)

  /** What a step is asked of: a store, or a structure known by its members. */
  private def asked(on: Term): Boolean = c.isStore(on.tpe.widen) || c.isStructure(on.tpe.widen)

  /** A call of a method of the developer's that uses a port. */
  def holderCall(t: Term): Boolean = c.isOwn(t.symbol) && c.kept(t.symbol).exists(d => uses(d.rhs.get, false))

  /** How many steps `t` takes at most: what numbers the steps after a conditional. */
  def count(t: Term): Int = c.bare(t) match
    case Block(stats, e)           => stats.collect { case ValDef(_, _, Some(rhs)) => count(rhs); case s: Term =>
      count(s) }.sum + count(e)
    case If(_, a, b)               => count(a).max(count(b))
    case call if storeCall(call)   => 1
    case call if holderCall(call)  => c.kept(call.symbol).fold(0)(d => count(d.rhs.get))
    case _                         => 0

  /** One step: a port's method called (an `update` method's body run as one, its `this` the port), or its state
    * read; among other calls, from the state they left.
    */
  def step(call: Term, as: TypeRepr)(rest: Rest)(using walk: Walk): DTerm[Any] =
    val on = receiver(call).getOrElse(c.refuse("a port used with no receiver", call))
    val at = placeOf(on)
    interfered(at.key) { now =>
      if !isUpdate(call.symbol) then rest(c.read(call, as)(using now.env), now)
      else if c.isStructure(on.tpe.widen) then wired(call, on, at)(rest)(using now)
      else inlined(call, at)(rest)(using now)
    }

  /** A call that changes a structure the class holds: the member's word applied to the structure's state and
    * the call's inputs (`Known.wiring`), its result with the state it leaves.
    */
  private def wired(call: Term, on: Term, at: Place)(rest: Rest)(using walk: Walk): DTerm[Any] =
    val state = stateIn(at)
    val given_ = state :: arguments(call, Nil).zip(c.inputsOf(on, call.symbol)).map((a, p) =>
      c.read(a, p)(using walk.env))
    val did = MemberCall.applied[Any](c.wired(on).member(call.symbol.name), given_)(using
      pair(c.spec(call.tpe.widen, call), state.rocqType).asInstanceOf[RocqType[Any]])
    c.bind(did, "did")(d => traced(at, c.fieldOf(d, "_2"))(rest(c.fieldOf(d, "_1"), _)))(using walk.out)

  /** An `update` method's body, run as one step from the port's state: a reading of its own, the port its root. */
  private def inlined(call: Term, at: Place)(rest: Rest)(using walk: Walk): DTerm[Any] =
    val m = call.symbol
    val d = c.kept(m).getOrElse(c.refuse(s"a call of `${m.name}`, whose body is not in the TASTy read", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil)).map((p, a) =>
      (p.symbol, c.read(a, p.tpt.tpe)(using walk.env)))
    val inside = Walk(walk.env ++ given_ + ((m.owner, stateIn(at))), walk.step, walk.between,
      Ports(m.owner, Map.empty, true), walk.out)
    run(d.rhs.get, d.returnTpt.tpe, m.owner)((v, after) => traced(at, after.env(m.owner))(rest(v, _)))(using inside)

  /** Where the reading is once a step left the state `left` at a place: the states it is part of made again, and,
    * among other calls, the step (the whole state it started from, the whole state it left) added to the traces.
    */
  private def traced(at: Place, left: DTerm[Any])(rest: Walk => DTerm[Any])(using walk: Walk): DTerm[Any] =
    val before = walk.whole
    putAt(at, left) { after =>
      if !walk.interleaved then rest(after)
      else named("trace", c.any(Among.stepped[Any](c.madeTraces(walk.env(trace)), before, after.whole)(using
        before.rocqType)))(t => rest(after.bound(trace, t)))(using after)
    }

  /** A call of a method of the developer's that uses a port: its body run where it is called, the port its
    * `this` or the parameter it is given to.
    */
  def called(call: Term)(rest: Rest)(using walk: Walk): DTerm[Any] =
    val m = call.symbol
    if walk.env.reading(m) then c.refuse(s"`${m.name}` calling itself: recursion is not read yet", call)
    val d = c.kept(m).getOrElse(c.refuse(s"a call of `${m.name}`, whose body is not in the TASTy read", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil))
    val (key, at) = given_.collectFirst { case (p, a) if c.isPort(p.tpt.tpe) => (p.symbol, placeOf(a)) }
      .getOrElse((m.owner, receiver(call).fold(Place(m.owner, Nil))(placeOf)))
    val up = if at == Place(key, Nil) then walk.ports.up else walk.ports.up + ((key, at))
    val from = walk.env.entering(m) ++ given_.map((p, a) => (p.symbol, c.read(a, p.tpt.tpe)(using walk.env))) +
      ((key, stateIn(at)))
    run(d.rhs.get, d.returnTpt.tpe, key)((v, after) => rest(v, walk.copy(env = walk.env ++ walk.ports.chain(
      at.key).map(k => (k, after.env(k))) ++ after.env.bound.get(trace).map((trace, _)).toList, step = after.step)))(
      using walk.copy(env = from, ports = walk.ports.copy(up = up)))

  /** What a method is called on, if anything. */
  def receiver(t: Term): Option[Term] = c.bare(t) match
    case Apply(f, _)     => receiver(f)
    case TypeApply(f, _) => receiver(f)
    case Select(on, _)   => Some(on)
    case _               => None

  /** The arguments a call is given, over every list. */
  def arguments(t: Term, after: List[Term]): List[Term] = t match
    case Apply(f, args)  => arguments(f, args ++ after)
    case TypeApply(f, _) => arguments(f, after)
    case _               => after
