package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
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
        case Select(on, _) if !changing && r.isStore(on.tpe.widen)     => true
        case s: Select if through(s.symbol)                            => true
        case other                                                     => foldOverTree(seen, other)(owner))
      def through(m: Symbol): Boolean =
        !within(m) && r.isOwn(m) && r.kept(m).exists(d => uses(d.rhs.get, changing, within + m))
    found.foldTree(false, t)(Symbol.spliceOwner)

  /** A call of a store's method, or a read of its state: one step. */
  def storeCall(t: Term): Boolean = receiver(t).exists(on => r.isStore(on.tpe.widen))

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
  def step[Out: Type](call: Term, as: TypeRepr, key: Symbol)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] = interfered[Out](key) { at =>
    val m = call.symbol
    if !isUpdate(m) then rest(r.read(call, as)(using at.env), at)
    else
      val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep", call))
      modelled[Out](call, d, key)(rest)(using at).getOrElse {
        val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil)).map((p, a) =>
          (p.symbol, r.read(a, p.tpt.tpe)(using at.env)))
        val inside = at.copy(env = at.env ++ given_ + ((m.owner, at.env(key))), atomic = true)
        run(d.rhs.get, d.returnTpt.tpe, m.owner)((v, after) =>
          traced[Out](at, key, after.env(m.owner))(rest(v, _)))(using inside)
      }
  }

  /** A call of a store's method from a service's code as a call of the method's Definition, the one of its name
    * in the store's companion (from the state and the argument, the result with the state left): the service is
    * then proven from what the store's contracts say of it. A store's own code is its methods' bodies.
    */
  private def modelled[Out: Type](call: Term, d: DefDef, key: Symbol)(rest: Rest[Out])(using at: Walk)(using Quotes)
      : Option[Expr[DTerm[Out]]] =
    val model = call.symbol.owner.companionModule.declaredField(call.symbol.name)
    (d.termParamss.flatMap(_.params), arguments(call, Nil)) match
      case (List(p), List(arg)) if !model.isNoSymbol && !ofStore =>
        (stateOf(key).asType, p.tpt.tpe.asType, d.returnTpt.tpe.asType) match
          case ('[s], '[a], '[v]) if model.termRef.widen <:< TypeRepr.of[Defined[(s, a) => (v, s)]] =>
            val site = Literal(UnitConstant())
            Some('{ Terms.let[(v, s), Out](Defined.apply[s, a, (v, s)](${ Ref(model).asExprOf[Defined[(s, a) =>
              (v, s)]] })(${ at.env(key).asExprOf[DTerm[s]] }, ${ r.readAs[a](arg)(using at.env) })(using
              ${ r.spec[s](site) }, ${ r.spec[a](site) }, ${ r.spec[(v, s)](site) }), "did", (did: DTerm[(v, s)]) =>
              ${ traced[Out](at, key, '{ TermSyntax._2[v, s](did)(using ${ r.spec[s](site) }) })(
                rest('{ TermSyntax._1[v, s](did)(using ${ r.spec[v](site) }) }, _)) })(using ${ r.spec[Out](site) }) })
          case _ => None
      case _ => None

  /** Where the reading is once a step left the state `left`: the state bound, and, among other calls, the step
    * (the state it started from, the state it left) added to the trace.
    */
  private def traced[Out: Type](at: Walk, key: Symbol, left: Expr[DTerm[?]])(rest: Walk => Quotes ?=> Expr[DTerm[Out]])(
      using Quotes): Expr[DTerm[Out]] = stateOf(key).asType match
    case '[s] if at.interleaved => named[Out]("trace", TypeRepr.of[List[(s, s)]], '{ TermSyntax.:+[(s, s)](
      ${ at.env(trace).asExprOf[DTerm[List[(s, s)]]] })(LiftOps.pair[s, s](${ at.env(key).asExprOf[DTerm[s]] },
      ${ left.asExprOf[DTerm[s]] })(using ${ r.spec[(s, s)](Literal(UnitConstant())) })) })(t =>
      rest(at.bound(key, left).bound(trace, t)))
    case _                      => rest(at.bound(key, left))

  /** The state a step starts from: among other calls, and after the call's first step, what they left. */
  private def interfered[Out: Type](key: Symbol)(body: Walk => Quotes ?=> Expr[DTerm[Out]])(using walk: Walk)(
      using Quotes): Expr[DTerm[Out]] =
    val next = walk.copy(step = walk.step + 1)
    (walk.between, others, stateOf(key).asType) match
      case (Some((between, input)), Some(rely), '[s]) if walk.interleaved && walk.step >= 1 => input match
        case '{ $x: DTerm[a] } =>
          val site = Literal(UnitConstant())
          val before = walk.env(key).asExprOf[DTerm[s]]
          '{ Terms.let[s, Out](Among.admitted[a, s]($before, Among.left[s]($before,
            ${ between.asExprOf[DTerm[Map[BigInt, s]]] }, BigInt(${ Expr(next.step) })))(
            ${ rely.asExprOf[Defined[(a, s, s) => Boolean]] }, $x)(using ${ r.spec[a](site) }, ${ r.spec[s](site) }),
            "now", (now: DTerm[s]) => ${ body(next.bound(key, 'now)) })(using ${ r.spec[Out](site) }) }
      case _                                                                                => body(next)

  /** A call of a method of the developer's that uses a port: its body run where it is called, the port the
    * parameter it is given to, or the method's `this`.
    */
  def called[Out: Type](call: Term, key: Symbol)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] =
    val m = call.symbol
    if walk.env.reading(m) then r.refuse(s"`${m.name}` calling itself: recursion is not read yet", call)
    val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil))
    val port = given_.collectFirst { case (p, _) if r.isPort(p.tpt.tpe) => p.symbol }.getOrElse(m.owner)
    val self = receiver(call).filter(_ => port == m.owner).map(on => (m.owner, r.read(on, on.tpe.widen)(
      using walk.env))).toList
    val from = walk.env.entering(m) ++ given_.map((p, a) => (p.symbol, r.read(a, p.tpt.tpe)(using walk.env))) ++ self
    run(d.rhs.get, d.returnTpt.tpe, port)((v, after) => rest(v, after.copy(env = walk.env ++ carried(port)(
      using after).map((k, term) => (if k == port then key else k, term)))))(using walk.copy(env = from))

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
