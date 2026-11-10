package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.TermSyntax
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** Where a reading of Scala that changes a port is (`StepReader`), and what it carries from one step to the next:
  * the store's state, and, among other calls, the trace of what each step did.
  */
private[steps] trait StepWalk:
  this: StepReader =>
  import r.q.reflect.*

  /** Where a reading is: the variables in scope, how many steps were taken, the schedule of what other calls do
    * between steps with the call's input (when read among them), and whether it is inside one step (an `update`
    * method's body).
    */
  final case class Walk(env: r.Env, step: Int, between: Option[(Expr[DTerm[?]], Expr[DTerm[?]])], atomic: Boolean):
    def bound(key: Symbol, term: Expr[DTerm[?]]): Walk = copy(env = env + ((key, term)))
    def interleaved: Boolean = between.nonEmpty && !atomic

  /** What follows a step: given the step's value and where the reading is after it, the rest's term. */
  type Rest[Out] = (Expr[DTerm[?]], Walk) => Quotes ?=> Expr[DTerm[Out]]

  /** The key the trace is bound to among the variables: a symbol no Scala names. */
  lazy val trace: Symbol =
    Symbol.newVal(Symbol.spliceOwner, "trace$", defn.UnitClass.typeRef, Flags.EmptyFlags, Symbol.noSymbol)

  /** The port's class: `key` itself in a method's body, else the class of the variable `key` is. */
  def portOf(key: Symbol): Symbol = if key.isClassDef then key else key.termRef.widen.typeSymbol

  def stateOf(key: Symbol): TypeRepr = r.stateType(portOf(key).typeRef, Literal(UnitConstant()))

  /** What is carried from a step to the next: the state `key` is bound to, and the trace when there is one. */
  def carried(key: Symbol)(using walk: Walk): List[(Symbol, Expr[DTerm[?]])] =
    (key, walk.env(key)) :: Option.when(walk.between.nonEmpty)((trace, walk.env(trace))).toList

  private def carriedType(key: Symbol)(using walk: Walk)(using Quotes): TypeRepr = stateOf(key).asType match
    case '[s] => if walk.between.nonEmpty then TypeRepr.of[(s, List[(s, s)])] else TypeRepr.of[s]

  /** The type of a value with what is carried after it: `(V, S)`, among other calls `(V, (S, trace))`. */
  def packedType(as: TypeRepr, key: Symbol)(using Walk)(using Quotes): TypeRepr =
    (as.asType, carriedType(key).asType) match
      case ('[v], '[c]) => TypeRepr.of[(v, c)]
      case _            => r.refuse("this value", Literal(UnitConstant()))

  /** A value with what is carried after it, as one term. */
  def packed(v: Expr[DTerm[?]], as: TypeRepr, key: Symbol)(using walk: Walk)(using Quotes): Expr[DTerm[?]] =
    (as.asType, stateOf(key).asType) match
      case ('[v], '[s]) if walk.between.nonEmpty =>
        '{ LiftOps.pair[v, (s, List[(s, s)])](${ v.asExprOf[DTerm[v]] }, LiftOps.pair[s, List[(s, s)]](
          ${ walk.env(key).asExprOf[DTerm[s]] }, ${ walk.env(trace).asExprOf[DTerm[List[(s, s)]]] })(using
          ${ r.spec[(s, List[(s, s)])](Literal(UnitConstant())) }))(using
          ${ r.spec[(v, (s, List[(s, s)]))](Literal(UnitConstant())) }) }
      case ('[v], '[s])                          =>
        '{ LiftOps.pair[v, s](${ v.asExprOf[DTerm[v]] }, ${ walk.env(key).asExprOf[DTerm[s]] })(using
          ${ r.spec[(v, s)](Literal(UnitConstant())) }) }
      case _                                     => r.refuse("this value", Literal(UnitConstant()))

  /** The value and what is carried, taken from one term (`packed`). */
  def unpacked(p: Expr[DTerm[?]], as: TypeRepr, key: Symbol)(using walk: Walk)(using Quotes)
      : (Expr[DTerm[?]], List[(Symbol, Expr[DTerm[?]])]) = (as.asType, stateOf(key).asType) match
    case ('[v], '[s]) if walk.between.nonEmpty =>
      val at = Literal(UnitConstant())
      val rest = '{ TermSyntax._2[v, (s, List[(s, s)])](${ p.asExprOf[DTerm[(v, (s, List[(s, s)]))]] })(using
        ${ r.spec[(s, List[(s, s)])](at) }) }
      ('{ TermSyntax._1[v, (s, List[(s, s)])](${ p.asExprOf[DTerm[(v, (s, List[(s, s)]))]] })(using
        ${ r.spec[v](at) }) }, List((key, '{ TermSyntax._1[s, List[(s, s)]]($rest)(using ${ r.spec[s](at) }) }),
        (trace, '{ TermSyntax._2[s, List[(s, s)]]($rest)(using ${ r.spec[List[(s, s)]](at) }) })))
    case ('[v], '[s])                          =>
      val at = Literal(UnitConstant())
      ('{ TermSyntax._1[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using ${ r.spec[v](at) }) },
        List((key, '{ TermSyntax._2[v, s](${ p.asExprOf[DTerm[(v, s)]] })(using ${ r.spec[s](at) }) })))
    case _                                     => r.refuse("this value", Literal(UnitConstant()))
