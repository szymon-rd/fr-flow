package frflow
package program

import scala.quoted.*

/** `Node.contract(id, statement)(forall((a, b) => … op(a, b) …))`: the operation a contract written as a claim is
  * about, found as it compiles, so the node has the operation's type and a formula of another shape does not compile.
  */
private[frflow] object ContractMacros:
  private val Shape = "a contract written as a claim applies one operation to its forall's variables, in order: " +
    "forall((held: Term[List[Booking]], request: Term[Booking]) => … granted(held, request) …)"

  def claimShaped(statement: Expr[String], formula: Expr[Term[Boolean]])(using Quotes): Expr[Node[?]] =
    import quotes.reflect.*
    val body = formula.asTerm
    val bound = variables(body)
    val calls = applications(body)
    calls.map(_._1.symbol).distinct match
      case Nil       => report.errorAndAbort(s"FrFlow: this formula applies no operation (a Param): $Shape", body.pos)
      case List(sym) =>
        calls.find((_, args) => args.map(_.symbol) != bound).foreach((op, args) =>
          report.errorAndAbort(s"FrFlow: ${op.show}(${args.map(_.show).mkString(", ")}): $Shape", args.headOption.fold(op.pos)(_.pos)))
        if references(body, sym) > calls.size then
          report.errorAndAbort(s"FrFlow: ${sym.name} is used other than applied to the forall's variables: $Shape", body.pos)
        val op = calls.head._1
        op.tpe.widen.asType match
          case '[Param[f]] =>
            if TypeRepr.of[f].typeArgs.lastOption.exists(_ <:< TypeRepr.of[Flow[?]]) then
              report.errorAndAbort(s"FrFlow: ${op.show} runs a flow: its contract is written as a lambda over the run", op.pos)
            val p = op.asExprOf[Param[f]]
            '{ Node.claimShaped[f]($p, Source.nodeId, $statement, Lifted.thunk(() => $formula, Source.text($formula)),
              ${ SourceMacros.here }, ${ SourceMacros.at }) }
          case _ => report.errorAndAbort(s"FrFlow: ${op.show} is not a Param: $Shape", op.pos)
      case many => report.errorAndAbort(s"FrFlow: this formula applies ${many.map(_.name).mkString(" and ")}: $Shape", body.pos)

  private def unwrap(using q: Quotes)(t: q.reflect.Term): q.reflect.Term =
    import q.reflect.*
    t match
      case Inlined(_, _, b) => unwrap(b)
      case Typed(b, _)      => unwrap(b)
      case Block(Nil, b)    => unwrap(b)
      case _                => t

  /** The variables of the forall around the formula, if it is one. */
  private def variables(using q: Quotes)(t: q.reflect.Term): List[q.reflect.Symbol] =
    import q.reflect.*
    unwrap(t) match
      case Apply(Apply(fn, List(Lambda(params, _))), _) if fn.symbol.name == "forall" => params.map(_.symbol)
      case Apply(fn, List(Lambda(params, _))) if fn.symbol.name == "forall"           => params.map(_.symbol)
      case _                                                                         => Nil

  /** Each `p(args)` with `p` a Param, and the arguments as written. */
  private def applications(using q: Quotes)(t: q.reflect.Term): List[(q.reflect.Term, List[q.reflect.Term])] =
    import q.reflect.*
    val param = TypeRepr.of[Param[?]]
    val found = List.newBuilder[(Term, List[Term])]
    object Calls extends TreeTraverser:
      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case Apply(Apply(fn, List(p)), args) if fn.symbol.name == "apply" && p.tpe.widen <:< param =>
            found += unwrap(p) -> args.map(unwrap)
          case _ => ()
        super.traverseTree(tree)(owner)
    Calls.traverseTree(t)(Symbol.spliceOwner)
    found.result()

  /** How many times the formula names `sym`. */
  private def references(using q: Quotes)(t: q.reflect.Term, sym: q.reflect.Symbol): Int =
    import q.reflect.*
    var n = 0
    object Refs extends TreeTraverser:
      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case r: Ref if r.symbol == sym => n += 1
          case _                         => ()
        super.traverseTree(tree)(owner)
    Refs.traverseTree(t)(Symbol.spliceOwner)
    n
