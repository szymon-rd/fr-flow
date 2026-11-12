package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.service.Call as ServiceCall
import frflow.dsl.term.{Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** The calls the reader of Scala that changes a port follows (`StepReader`): of a store's method (one step: among
  * other calls, they may have changed the store before it), of a service's or another of the developer's methods
  * (its body, read where it is called), and what is carried from one step to the next: the store's state, and,
  * among other calls, the trace of what each step did.
  */
private[steps] trait StepCalls:
  this: StepReader =>
  import r.q.reflect.*

  def isUpdate(m: Symbol): Boolean = m.isDefDef && m.flags.is(Flags.Mutable)

  /** Whether `t` needs no step: read alone or inside one step, it changes no port; among others, it uses none. */
  def quiet(t: Term)(using walk: Walk): Boolean = if walk.interleaved then !uses(t, false) else !uses(t, true)

  /** Whether `t` uses a store (`changing`: changes one): directly, or through a method of the developer's. */
  private def uses(t: Term, changing: Boolean, within: Set[Symbol] = Set.empty): Boolean =
    val found = new TreeAccumulator[Boolean]:
      def foldTree(seen: Boolean, tree: Tree)(owner: Symbol): Boolean = seen || (tree match
        case Assign(_, _)                                              => true
        case a: Apply if isUpdate(a.symbol) || through(a.symbol)        => true
        case Select(on, _) if !changing && asked(on)                   => true
        case s: Select if through(s.symbol)                            => true
        case other                                                     => foldOverTree(seen, other)(owner))
      def through(m: Symbol): Boolean =
        !within(m) && r.isOwn(m) && r.kept(m).exists(d => uses(d.rhs.get, changing, within + m))
    found.foldTree(false, t)(Symbol.spliceOwner)

  /** A call of a store's method, or a read of its state: one step. */
  def storeCall(t: Term): Boolean = receiver(t).exists(asked)

  /** What a step is asked of: a store, or a service known by its members. */
  private def asked(on: Term): Boolean = r.isStore(on.tpe.widen) || r.isService(on.tpe.widen)

  /** A call of a method of the developer's that uses a port: a service's, or one given the port. */
  def serviceCall(t: Term): Boolean = r.isOwn(t.symbol) && r.kept(t.symbol).exists(d => uses(d.rhs.get, false))

  /** How many steps `t` takes at most: what numbers the steps after a conditional. */
  def count(t: Term): Int = r.bare(t) match
    case Block(stats, e)              => stats.collect { case ValDef(_, _, Some(rhs)) => count(rhs); case s: Term =>
      count(s) }.sum + count(e)
    case If(_, a, b)                  => count(a).max(count(b))
    case call if storeCall(call)      => 1
    case call if serviceCall(call)    => r.kept(call.symbol).fold(0)(d => count(d.rhs.get))
    case _                            => 0

  /** One step: a store's method called (an `update` method's body run as one, its `this` the store), or its state
    * read; among other calls, from the state they left.
    */
  def step[Out: Type](call: Term, as: TypeRepr)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] =
    val on = receiver(call).getOrElse(r.refuse("a store used with no receiver", call))
    val at = placeOf(on)
    interfered[Out](at.key) { now =>
      if !isUpdate(call.symbol) then rest(r.read(call, as)(using now.env), now)
      else if r.isService(on.tpe.widen) then wired[Out](call, on, at)(rest)(using now)
      else modelled[Out](call, at)(rest)(using now).getOrElse(inlined[Out](call, at)(rest)(using now))
    }

  /** A call that changes a service the code is given: the member's Definition applied to the service's state
    * and the call's inputs (`Services.wiring`), its result with the state it leaves.
    */
  private def wired[Out: Type](call: Term, on: Term, at: Place)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] = (stateAt(at).asType, call.tpe.widen.asType) match
    case ('[s], '[v]) =>
      val site = Literal(UnitConstant())
      val given_ = Expr.ofList(stateIn(at) :: arguments(call, Nil).zip(r.inputsOf(on, call.symbol)).map((a, p) =>
        r.read(a, p)(using walk.env)))
      '{ Terms.let[(v, s), Out](ServiceCall.applied[(v, s)](${ r.wired(on) }.member(${ Expr(call.symbol.name) }),
        $given_)(using ${ r.spec[(v, s)](site) }), "did", (did: DTerm[(v, s)]) =>
        ${ traced[Out](at, '{ TermSyntax._2[v, s](did)(using ${ r.spec[s](site) }) })(
          rest('{ TermSyntax._1[v, s](did)(using ${ r.spec[v](site) }) }, _)) })(using ${ r.spec[Out](site) }) }
    case _            => r.refuse("this call of a service", call)

  /** An `update` method's body, run as one step from the store's state: a reading of its own, the store its root. */
  private def inlined[Out: Type](call: Term, at: Place)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] =
    val m = call.symbol
    val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil)).map((p, a) =>
      (p.symbol, r.read(a, p.tpt.tpe)(using walk.env)))
    val inside = Walk(walk.env ++ given_ + ((m.owner, stateIn(at))), walk.step, walk.between,
      Ports(m.owner, Map.empty, true))
    run(d.rhs.get, d.returnTpt.tpe, m.owner)((v, after) =>
      traced[Out](at, after.env(m.owner))(rest(v, _)))(using inside)

  /** Whether a call is read as a call of its method's Definition: of a store's method always, of a service's
    * when the code is read alone (among other calls a service's method is its steps); and never of a method of
    * the port the code is read of, whose code this is.
    */
  private def known(call: Term)(using walk: Walk): Boolean =
    val owner = call.symbol.owner
    owner != portOf(walk.ports.root) && (r.isStore(owner.typeRef) || walk.between.isEmpty)

  /** A call of a port's method as a call of the method's Definition, the one of its name in the port's companion
    * (from the state and the argument, the result with the state left): the code is then proven from what the
    * port's contracts say of the method, not from the method's body.
    */
  def modelled[Out: Type](call: Term, at: Place)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Option[Expr[DTerm[Out]]] =
    val model = call.symbol.owner.companionModule.declaredField(call.symbol.name)
    val params = r.kept(call.symbol).toList.flatMap(_.termParamss.flatMap(_.params))
    (params, arguments(call, Nil)) match
      case (List(p), List(arg)) if !model.isNoSymbol && known(call) =>
        val result = r.kept(call.symbol).get.returnTpt.tpe
        (stateAt(at).asType, p.tpt.tpe.asType, result.asType) match
          case ('[s], '[a], '[v]) if model.termRef.widen <:< TypeRepr.of[Defined[(s, a) => (v, s)]] =>
            val site = Literal(UnitConstant())
            Some('{ Terms.let[(v, s), Out](Defined.apply[s, a, (v, s)](${ Ref(model).asExprOf[Defined[(s, a) =>
              (v, s)]] })(${ stateIn(at).asExprOf[DTerm[s]] }, ${ r.readAs[a](arg)(using walk.env) })(using
              ${ r.spec[s](site) }, ${ r.spec[a](site) }, ${ r.spec[(v, s)](site) }), "did", (did: DTerm[(v, s)]) =>
              ${ traced[Out](at, '{ TermSyntax._2[v, s](did)(using ${ r.spec[s](site) }) })(
                rest('{ TermSyntax._1[v, s](did)(using ${ r.spec[v](site) }) }, _)) })(using ${ r.spec[Out](site) }) })
          case _ => None
      case _ => None

  /** Where the reading is once a step left the state `left` at a place: the states it is part of made again, and,
    * among other calls, the step (the whole state it started from, the whole state it left) added to the trace.
    */
  private def traced[Out: Type](at: Place, left: Expr[DTerm[?]])(rest: Walk => Quotes ?=> Expr[DTerm[Out]])(
      using walk: Walk)(using Quotes): Expr[DTerm[Out]] =
    val before = walk.whole
    putAt[Out](at, left) { after =>
      stateOf(walk.ports.root).asType match
        case '[s] if walk.interleaved && serving =>
          named[Out]("trace", TypeRepr.of[Among.Traces[s]], '{ Among.stepped[s](
            ${ walk.env(trace).asExprOf[DTerm[Among.Traces[s]]] }, ${ before.asExprOf[DTerm[s]] },
            ${ after.whole.asExprOf[DTerm[s]] })(using ${ r.spec[s](Literal(UnitConstant())) }) })(t =>
            rest(after.bound(trace, t)))
        case '[s] if walk.interleaved            =>
          named[Out]("trace", TypeRepr.of[List[(s, s)]], '{ TermSyntax.:+[(s, s)](
            ${ walk.env(trace).asExprOf[DTerm[List[(s, s)]]] })(LiftOps.pair[s, s](${ before.asExprOf[DTerm[s]] },
            ${ after.whole.asExprOf[DTerm[s]] })(using ${ r.spec[(s, s)](Literal(UnitConstant())) })) })(t =>
            rest(after.bound(trace, t)))
        case _                                   => rest(after)
    }

  /** A call of a method of the developer's that uses a port: a call of its Definition when it has one (`modelled`),
    * else its body run where it is called, the port its `this` or the parameter it is given to.
    */
  def called[Out: Type](call: Term)(rest: Rest[Out])(using walk: Walk)(using Quotes): Expr[DTerm[Out]] =
    val m = call.symbol
    if walk.env.reading(m) then r.refuse(s"`${m.name}` calling itself: recursion is not read yet", call)
    val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil))
    val (key, at) = given_.collectFirst { case (p, a) if r.isPort(p.tpt.tpe) => (p.symbol, placeOf(a)) }
      .getOrElse((m.owner, receiver(call).fold(Place(m.owner, Nil))(placeOf)))
    def body(using Quotes): Expr[DTerm[Out]] =
      val up = if at == Place(key, Nil) then walk.ports.up else walk.ports.up + ((key, at))
      val from = walk.env.entering(m) ++ given_.map((p, a) => (p.symbol, r.read(a, p.tpt.tpe)(using walk.env))) +
        ((key, stateIn(at)))
      run(d.rhs.get, d.returnTpt.tpe, key)((v, after) => rest(v, walk.copy(env = walk.env ++ walk.ports.chain(
        at.key).map(k => (k, after.env(k))) ++ after.env.bound.get(trace).map((trace, _)).toList, step = after.step)))(
        using walk.copy(env = from, ports = walk.ports.copy(up = up)))
    Option.when(key == m.owner && !r.isStore(m.owner.typeRef))(at).flatMap(modelled[Out](call, _)(rest))
      .getOrElse(body)

  /** What a method is called on, if anything. */
  def receiver(t: Term): Option[Term] = r.bare(t) match
    case Apply(f, _)     => receiver(f)
    case TypeApply(f, _) => receiver(f)
    case Select(on, _)   => Some(on)
    case _               => None

  /** The arguments a call is given, over every list. */
  def arguments(t: Term, after: List[Term]): List[Term] = t match
    case Apply(f, args)  => arguments(f, args ++ after)
    case TypeApply(f, _) => arguments(f, after)
    case _               => after
