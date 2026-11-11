package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.TermSyntax
import frflow.dsl.term.Term as DTerm
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

  private def carriedType(using walk: Walk)(using Quotes): TypeRepr = stateOf(walk.ports.root).asType match
    case '[s] => if walk.between.nonEmpty then TypeRepr.of[(s, List[(s, s)])] else TypeRepr.of[s]

  /** The type of a value with what is carried after it: `(V, S)`, among other calls `(V, (S, trace))`. */
  def packedType(as: TypeRepr)(using Walk)(using Quotes): TypeRepr = (as.asType, carriedType.asType) match
    case ('[v], '[c]) => TypeRepr.of[(v, c)]
    case _            => r.refuse("this value", Literal(UnitConstant()))

  /** A value with what is carried after it, as one term. */
  def packed(v: Expr[DTerm[?]], as: TypeRepr)(using walk: Walk)(using Quotes): Expr[DTerm[?]] =
    val at = Literal(UnitConstant())
    (as.asType, stateOf(walk.ports.root).asType) match
      case ('[v], '[s]) if walk.between.nonEmpty =>
        '{ LiftOps.pair[v, (s, List[(s, s)])](${ v.asExprOf[DTerm[v]] }, LiftOps.pair[s, List[(s, s)]](
          ${ walk.whole.asExprOf[DTerm[s]] }, ${ walk.env(trace).asExprOf[DTerm[List[(s, s)]]] })(using
          ${ r.spec[(s, List[(s, s)])](at) }))(using ${ r.spec[(v, (s, List[(s, s)]))](at) }) }
      case ('[v], '[s])                          =>
        '{ LiftOps.pair[v, s](${ v.asExprOf[DTerm[v]] }, ${ walk.whole.asExprOf[DTerm[s]] })(using
          ${ r.spec[(v, s)](at) }) }
      case _                                     => r.refuse("this value", at)

  /** The value and what is carried, taken from one term (`packed`). */
  def unpacked(p: Expr[DTerm[?]], as: TypeRepr)(using walk: Walk)(using Quotes)
      : (Expr[DTerm[?]], List[(Symbol, Expr[DTerm[?]])]) =
    val at = Literal(UnitConstant())
    (as.asType, stateOf(walk.ports.root).asType) match
      case ('[v], '[s]) if walk.between.nonEmpty =>
        val rest = '{ TermSyntax._2[v, (s, List[(s, s)])](${ p.asExprOf[DTerm[(v, (s, List[(s, s)]))]] })(using
          ${ r.spec[(s, List[(s, s)])](at) }) }
        ('{ TermSyntax._1[v, (s, List[(s, s)])](${ p.asExprOf[DTerm[(v, (s, List[(s, s)]))]] })(using
          ${ r.spec[v](at) }) }, List((walk.ports.root, '{ TermSyntax._1[s, List[(s, s)]]($rest)(using
          ${ r.spec[s](at) }) }), (trace, '{ TermSyntax._2[s, List[(s, s)]]($rest)(using
          ${ r.spec[List[(s, s)]](at) }) })))
      case ('[v], '[s])                          =>
        ('{ TermSyntax._1[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using ${ r.spec[v](at) }) },
          List((walk.ports.root, '{ TermSyntax._2[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using
            ${ r.spec[s](at) }) })))
      case _                                     => r.refuse("this value", at)
