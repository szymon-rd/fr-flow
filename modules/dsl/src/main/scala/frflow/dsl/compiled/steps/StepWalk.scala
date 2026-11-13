package frflow.dsl.compiled.steps

import frflow.dsl.lifted.{FrSpec, LiftOps}
import frflow.dsl.lifted.steps.Among
import frflow.dsl.term.RocqType
import frflow.dsl.term.Term as DTerm

/** What a reading of Scala that changes a port carries from one step to the next (`Steps`): the whole state, and,
  * among other calls, what each step did and what the others did before it (`Among.Traces`).
  */
private[steps] trait StepWalk:
  this: Steps =>
  import c.q.reflect.*

  /** Where a reading is: the variables in scope, how many steps were taken, the schedule of what other calls do
    * between steps (when read among them), the ports it is over, and the type of what the whole reading gives.
    */
  final case class Walk(env: c.Env, step: Int, between: Option[DTerm[Any]], ports: Ports, out: RocqType[Any]):
    def bound(key: Symbol, term: DTerm[Any]): Walk = copy(env = env + ((key, term)))
    def interleaved: Boolean = between.nonEmpty && !ports.atomic
    /** The whole state: what the root is bound to. */
    def whole: DTerm[Any] = env(ports.root)

  /** What follows a step: given the step's value and where the reading is after it, the rest's term. */
  type Rest = (DTerm[Any], Walk) => DTerm[Any]

  /** The key the trace is bound to among the variables: a symbol no Scala names. */
  lazy val trace: Symbol =
    Symbol.newVal(Symbol.spliceOwner, "trace$", defn.UnitClass.typeRef, Flags.EmptyFlags, Symbol.noSymbol)

  def pair(a: RocqType[?], b: RocqType[?]): FrSpec[(Any, Any)] =
    FrSpec.pair[(Any, Any)](FrSpec.of(a), FrSpec.of(b))

  /** The traces' type over a state's: each step taken, and what other calls did before each. */
  def traces(state: RocqType[?]): FrSpec[Any] =
    val moves = FrSpec.list[Any](pair(state, state))
    pair(moves, moves).asInstanceOf[FrSpec[Any]]

  private def both(a: DTerm[Any], b: DTerm[Any]): DTerm[Any] =
    LiftOps.pair[Any, Any](a, b)(using pair(a.rocqType, b.rocqType)).asInstanceOf[DTerm[Any]]

  private def carried(using walk: Walk): DTerm[Any] =
    if walk.between.isEmpty then walk.whole else both(walk.whole, walk.env(trace))

  /** The type of a value with what is carried after it: `(V, S)`, among other calls `(V, (S, traces))`. */
  def packedType(value: RocqType[?])(using Walk): RocqType[Any] =
    pair(value, carried.rocqType).asInstanceOf[RocqType[Any]]

  /** A value with what is carried after it, as one term. */
  def packed(v: DTerm[Any])(using Walk): DTerm[Any] = both(v, carried)

  private def side(p: DTerm[Any], name: String): DTerm[Any] = p.selectDynamic(name).asInstanceOf[DTerm[Any]]

  /** The value and what is carried, taken from one term (`packed`). */
  def unpacked(p: DTerm[Any])(using walk: Walk): (DTerm[Any], List[(Symbol, DTerm[Any])]) =
    val rest = side(p, "_2")
    if walk.between.isEmpty then (side(p, "_1"), List((walk.ports.root, rest)))
    else (side(p, "_1"), List((walk.ports.root, side(rest, "_1")), (trace, side(rest, "_2"))))

  /** The state a step starts from: among other calls, and after the call's first step, whatever the schedule
    * says they left of the whole state, with what they did kept in the traces; a claim says what it takes of
    * them (`Call.others`).
    */
  def interfered(key: Symbol)(body: Walk => DTerm[Any])(using walk: Walk): DTerm[Any] =
    val next = walk.copy(step = walk.step + 1)
    walk.between match
      case Some(between) if walk.interleaved && walk.step >= 1 =>
        val before = next.whole
        given RocqType[Any] = before.rocqType
        c.bind(Among.left[Any](before, between.asInstanceOf[DTerm[Map[BigInt, Any]]],
          BigInt(next.step)).asInstanceOf[DTerm[Any]], "now")(now =>
          named("trace", Among.moved[Any](next.env(trace).asInstanceOf[DTerm[Among.Traces[Any]]], before, now)
            .asInstanceOf[DTerm[Any]])(t =>
            body(derived(key)(using next.bound(next.ports.root, now).bound(trace, t))))(using next))(using walk.out)
      case _                                                   => body(next)

  /** A value named for what follows it (a `let`). */
  def named(name: String, value: DTerm[Any])(rest: DTerm[Any] => DTerm[Any])(using walk: Walk): DTerm[Any] =
    c.bind(value, name)(rest)(using walk.out)
