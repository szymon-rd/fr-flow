package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.{Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** Where a reading of Scala that changes a port is (`StepReader`), and what it carries from one step to the next:
  * the state of the port the code is read of (the root's), and, among other calls, the trace of what each step
  * did.
  */
private[steps] trait StepWalk extends StepPorts:
  this: StepReader =>
  import r.q.reflect.*

  /** Where a reading is: the variables in scope, how many steps were taken, the schedule of what other calls do
    * between steps with the call's input (when read among them), and the ports it is over.
    */
  final case class Walk(env: r.Env, step: Int, between: Option[(Expr[DTerm[?]], Expr[DTerm[?]])], ports: Ports):
    def bound(key: Symbol, term: Expr[DTerm[?]]): Walk = copy(env = env + ((key, term)))
    def interleaved: Boolean = between.nonEmpty && !ports.atomic
    /** The whole state: what the root is bound to. */
    def whole: Expr[DTerm[?]] = env(ports.root)

  /** What follows a step: given the step's value and where the reading is after it, the rest's term. */
  type Rest[Out] = (Expr[DTerm[?]], Walk) => Quotes ?=> Expr[DTerm[Out]]

  /** The key the trace is bound to among the variables: a symbol no Scala names. */
  lazy val trace: Symbol =
    Symbol.newVal(Symbol.spliceOwner, "trace$", defn.UnitClass.typeRef, Flags.EmptyFlags, Symbol.noSymbol)

  /** What is carried from a step to the next: the whole state, and the trace when there is one. */
  def carried(using walk: Walk): List[(Symbol, Expr[DTerm[?]])] =
    (walk.ports.root, walk.whole) :: Option.when(walk.between.nonEmpty)((trace, walk.env(trace))).toList

  /** Whether the reading is of a structure's member among other calls (`MemberCode`): no rely is given it. */
  def serving(using walk: Walk): Boolean = walk.between.nonEmpty && others.isEmpty

  /** The trace's type over the state `s`: each step taken (the state it started from, the one it left); of a
    * structure's member, with what other calls did before each step (`Among.Traces`).
    */
  def traceType(s: TypeRepr)(using Walk)(using Quotes): TypeRepr = s.asType match
    case '[s] => if serving then TypeRepr.of[Among.Traces[s]] else TypeRepr.of[List[(s, s)]]

  private def carriedType(using walk: Walk)(using Quotes): TypeRepr =
    val s = stateOf(walk.ports.root)
    if walk.between.isEmpty then s else (s.asType, traceType(s).asType) match
      case ('[s], '[t]) => TypeRepr.of[(s, t)]
      case _            => r.refuse("this state", Literal(UnitConstant()))

  /** The type of a value with what is carried after it: `(V, S)`, among other calls `(V, (S, trace))`. */
  def packedType(as: TypeRepr)(using Walk)(using Quotes): TypeRepr = (as.asType, carriedType.asType) match
    case ('[v], '[c]) => TypeRepr.of[(v, c)]
    case _            => r.refuse("this value", Literal(UnitConstant()))

  /** A value with what is carried after it, as one term. */
  def packed(v: Expr[DTerm[?]], as: TypeRepr)(using walk: Walk)(using Quotes): Expr[DTerm[?]] =
    val (at, s) = (Literal(UnitConstant()), stateOf(walk.ports.root))
    (as.asType, s.asType, traceType(s).asType) match
      case ('[v], '[s], '[t]) if walk.between.nonEmpty =>
        '{ LiftOps.pair[v, (s, t)](${ v.asExprOf[DTerm[v]] }, LiftOps.pair[s, t](
          ${ walk.whole.asExprOf[DTerm[s]] }, ${ walk.env(trace).asExprOf[DTerm[t]] })(using
          ${ r.spec[(s, t)](at) }))(using ${ r.spec[(v, (s, t))](at) }) }
      case ('[v], '[s], _)                             =>
        '{ LiftOps.pair[v, s](${ v.asExprOf[DTerm[v]] }, ${ walk.whole.asExprOf[DTerm[s]] })(using
          ${ r.spec[(v, s)](at) }) }
      case _                                           => r.refuse("this value", at)

  /** The value and what is carried, taken from one term (`packed`). */
  def unpacked(p: Expr[DTerm[?]], as: TypeRepr)(using walk: Walk)(using Quotes)
      : (Expr[DTerm[?]], List[(Symbol, Expr[DTerm[?]])]) =
    val (at, s) = (Literal(UnitConstant()), stateOf(walk.ports.root))
    (as.asType, s.asType, traceType(s).asType) match
      case ('[v], '[s], '[t]) if walk.between.nonEmpty =>
        val rest = '{ TermSyntax._2[v, (s, t)](${ p.asExprOf[DTerm[(v, (s, t))]] })(using
          ${ r.spec[(s, t)](at) }) }
        ('{ TermSyntax._1[v, (s, t)](${ p.asExprOf[DTerm[(v, (s, t))]] })(using ${ r.spec[v](at) }) },
          List((walk.ports.root, '{ TermSyntax._1[s, t]($rest)(using ${ r.spec[s](at) }) }),
            (trace, '{ TermSyntax._2[s, t]($rest)(using ${ r.spec[t](at) }) })))
      case ('[v], '[s], _)                             =>
        ('{ TermSyntax._1[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using ${ r.spec[v](at) }) },
          List((walk.ports.root, '{ TermSyntax._2[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using
            ${ r.spec[s](at) }) })))
      case _                                           => r.refuse("this value", at)

  /** The state a step starts from: among other calls, and after the call's first step, what they left of the
    * whole state, with the state at `key` and those above it read from that.
    */
  def interfered[Out: Type](key: Symbol)(body: Walk => Quotes ?=> Expr[DTerm[Out]])(using walk: Walk)(
      using Quotes): Expr[DTerm[Out]] =
    val next = walk.copy(step = walk.step + 1)
    (walk.between, others, stateOf(walk.ports.root).asType) match
      case (Some((between, input)), Some(rely), '[s]) if walk.interleaved && walk.step >= 1 => input match
        case '{ $x: DTerm[a] } =>
          val site = Literal(UnitConstant())
          val before = walk.whole.asExprOf[DTerm[s]]
          '{ Terms.let[s, Out](Among.admitted[a, s]($before, Among.left[s]($before,
            ${ between.asExprOf[DTerm[Map[BigInt, s]]] }, BigInt(${ Expr(next.step) })))(
            ${ rely.asExprOf[Defined[(a, s, s) => Boolean]] }, $x)(using ${ r.spec[a](site) }, ${ r.spec[s](site) }),
            "now", (now: DTerm[s]) => ${ body(derived(key)(using next.bound(next.ports.root, 'now))) })(using
            ${ r.spec[Out](site) }) }
      case (Some((between, _)), None, '[s]) if walk.interleaved && walk.step >= 1           =>
        served[s, Out](between.asExprOf[DTerm[Map[BigInt, s]]], key, next)(body)
      case _                                                                                => body(next)

  /** The same of a structure's member (`MemberCode`): whatever the schedule says the others left, with what they
    * did kept in the traces; a claim says what it takes of them (`Call.others`).
    */
  private def served[S: Type, Out: Type](between: Expr[DTerm[Map[BigInt, S]]], key: Symbol, next: Walk)(
      body: Walk => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[DTerm[Out]] =
    val site = Literal(UnitConstant())
    val before = next.whole.asExprOf[DTerm[S]]
    '{ Terms.let[S, Out](Among.left[S]($before, $between, BigInt(${ Expr(next.step) })), "now", (now: DTerm[S]) =>
      ${ named[Out]("trace", TypeRepr.of[Among.Traces[S]], '{ Among.moved[S](
        ${ next.env(trace).asExprOf[DTerm[Among.Traces[S]]] }, $before, now)(using ${ r.spec[S](site) }) })(t =>
        body(derived(key)(using next.bound(next.ports.root, 'now).bound(trace, t)))) })(using
      ${ r.spec[Out](site) }) }
