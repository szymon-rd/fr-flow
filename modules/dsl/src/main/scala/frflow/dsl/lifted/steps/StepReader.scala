package frflow.dsl.lifted.steps

import frflow.core.name.DefName
import frflow.dsl.build.{Source, WrittenAt}
import frflow.dsl.lifted.{LiftOps, Lifted, Lifting, Reader}
import frflow.dsl.term.{Lift, Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** Scala that changes a port, read into state passing, as Aeneas reads Rust's `&mut`: the port's variable stands for
  * its state; a call of an `update` method is the state its body leaves; what follows a change reads the new state;
  * a conditional that changes the state gives the state either branch leaves. What changes nothing is read by the
  * reader of lifted code (`r`). Sound because the port is the code's alone, which Scala's separation checking
  * checks where the code is compiled.
  */
private[steps] final class StepReader(val r: Reader):
  import r.q.reflect.*

  /** What follows a step: given the step's value and the variables after it, the rest's term. */
  private type Rest[Out] = (Expr[DTerm[?]], r.Env) => Quotes ?=> Expr[DTerm[Out]]

  def updating[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using Quotes): Expr[Updating[P, S, A, R]] =
    val (name, file) = (r.defining.name, Source.relative(Position.ofMacroExpansion.sourceFile.path))
    '{ Updating[P, S, A, R](Lifted.Of2(Lifting.two[S, A, (R, S)](DefName(${ Expr(name) }),
      WrittenAt.in(Source.path(${ Expr(file) })), Source.of($f))(${ steps[P, S, A, R](f) })(
      using ${ r.spec[S](f.asTerm) }, ${ r.spec[A](f.asTerm) }, ${ r.spec[(R, S)](f.asTerm) }),
      (before: S, a: A) => ${ pure[P, S, A, R](f, 'before, 'a) }), $f) }

  /** The type of a port's state, as the witness the compiler finds for the port (`PortState.derived`). */
  def state[P: Type](using Quotes): Expr[PortState[P]] =
    val port = TypeRepr.of[P].typeSymbol
    TypeRepr.of[P].memberType(r.stateOf(port, Literal(UnitConstant()))).asType match
      case '[s] => '{ new PortState[P] { type S = s } }

  /** The Scala run on a port made from a state: its result, with the port's state after it. */
  private def pure[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R], before: Expr[S], a: Expr[A])(
      using Quotes): Expr[(R, S)] =
    val port = TypeRepr.of[P].typeSymbol
    val made = Apply(Select(New(TypeTree.of[P]), port.primaryConstructor), List(before.asTerm)).asExprOf[P]
    '{ val p = $made; val out = $f(p, $a); (out, ${ Select('p.asTerm, r.stateOf(port, f.asTerm)).asExprOf[S] }) }

  private def steps[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using Quotes)
      : Expr[(DTerm[S], DTerm[A]) => DTerm[(R, S)]] = r.bare(f.asTerm) match
    case Lambda(List(p, a), code) => '{ (state: DTerm[S], x: DTerm[A]) => ${
      run[(R, S)](code, TypeRepr.of[R], p.symbol)((v, env) => '{ LiftOps.pair[R, S](${ v.asExprOf[DTerm[R]] },
        ${ env(p.symbol).asExprOf[DTerm[S]] })(using ${ r.spec[(R, S)](code) }) })(
        using r.Env.of((p.symbol, 'state), (a.symbol, 'x))) } }
    case other                    => r.refuse("a function that is not a lambda of a port and an input", other)

  /** `t` run from the state `key` is bound to: its value and the variables after it, given to what follows. */
  private def run[Out: Type](t: Term, as: TypeRepr, key: Symbol)(rest: Rest[Out])(using env: r.Env)(using Quotes)
      : Expr[DTerm[Out]] = r.bare(t) match
    case pure if !changes(pure)                          => rest(r.read(pure, as), env)
    case Block(Nil, e)                                   => run(e, as, key)(rest)
    case Block((v @ ValDef(_, tpt, Some(rhs))) :: ss, e) => run(rhs, tpt.tpe.widen, key)((x, after) =>
      named[Out](v.name, tpt.tpe.widen, x)(y => run(Block(ss, e), as, key)(rest)(using after + ((v.symbol, y)))))
    case Block((s: Term) :: ss, e)                       =>
      run(s, s.tpe.widen, key)((_, after) => run(Block(ss, e), as, key)(rest)(using after))
    case Assign(to, value) if to.symbol == r.stateOf(portOf(key), t) => assigned(value, to, key)(rest)
    case branch @ If(c, _, _) if !changes(c)             => either(branch, as, key)(rest)
    case call @ Apply(Select(_, _), _) if isUpdate(call.symbol) => update(call, key)(rest)
    case call: Apply if changing(call.symbol, Set.empty) => called(call, key)(rest)
    case other                                           =>
      r.refuse("a change of a port here: a port changes in a statement, an `if`, or an `update` method's body", other)

  /** The state a `var`'s assignment leaves: the value assigned, named for what follows. */
  private def assigned[Out: Type](value: Term, to: Term, key: Symbol)(rest: Rest[Out])(using r.Env)(using Quotes)
      : Expr[DTerm[Out]] = run(value, to.tpe.widen, key)((x, after) =>
    named[Out](to.symbol.name, to.tpe.widen, x)(y => rest('{ Lift.constant[Unit](()) }, after + ((key, y)))))

  /** A call of an `update` method on the port: its body run from the port's state, its `this` the port. */
  private def update[Out: Type](call: Apply, key: Symbol)(rest: Rest[Out])(using env: r.Env)(using Quotes)
      : Expr[DTerm[Out]] =
    val (m, on) = (call.symbol, receiver(call))
    val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep " +
      "(-Yretain-trees)", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil)).map((p, a) =>
      (p.symbol, r.read(a, p.tpt.tpe)))
    val from = env ++ given_ + ((m.owner, r.read(on, on.tpe.widen)))
    run(d.rhs.get, d.returnTpt.tpe, m.owner)((v, after) => rest(v, env + ((key, after(m.owner)))))(using from)

  /** A call of a method of the developer's that changes the port it is given (a service method written as an
    * ordinary `def`): its body run from the port's state, the parameter the port is given to standing for it.
    */
  private def called[Out: Type](call: Apply, key: Symbol)(rest: Rest[Out])(using env: r.Env)(using Quotes)
      : Expr[DTerm[Out]] =
    val m = call.symbol
    if env.reading(m) then r.refuse(s"`${m.name}` calling itself: recursion is not read yet", call)
    val d = r.kept(m).getOrElse(r.refuse(s"a call of `${m.name}`, whose body the compiler did not keep", call))
    val given_ = d.termParamss.flatMap(_.params).zip(arguments(call, Nil))
    val port = given_.collectFirst { case (p, _) if r.isPort(p.tpt.tpe) => p.symbol }
      .getOrElse(r.refuse(s"a call of `${m.name}`, which is given no port", call))
    val from = env.entering(m) ++ given_.map((p, a) => (p.symbol, r.read(a, p.tpt.tpe)))
    run(d.rhs.get, d.returnTpt.tpe, port)((v, after) => rest(v, env + ((key, after(port)))))(using from)

  /** What a method is called on. */
  private def receiver(t: Term): Term = t match
    case Apply(f, _)     => receiver(f)
    case TypeApply(f, _) => receiver(f)
    case Select(on, _)   => on
    case other           => r.refuse("a call with no receiver", other)

  /** The arguments a call is given, over every list. */
  private def arguments(t: Term, after: List[Term]): List[Term] = t match
    case Apply(f, args)  => arguments(f, args ++ after)
    case TypeApply(f, _) => arguments(f, after)
    case _               => after

  /** A conditional that changes the state: its value with the state either branch leaves, named for what follows. */
  private def either[Out: Type](branch: If, as: TypeRepr, key: Symbol)(rest: Rest[Out])(using env: r.Env)(
      using Quotes): Expr[DTerm[Out]] = (as.asType, stateType(key).asType) match
    case ('[v], '[s]) =>
      def after(t: Term): Expr[DTerm[(v, s)]] = run[(v, s)](t, as, key)((x, left) => '{ LiftOps.pair[v, s](
        ${ x.asExprOf[DTerm[v]] }, ${ left(key).asExprOf[DTerm[s]] })(using ${ r.spec[(v, s)](t) }) })
      val at = branch.thenp
      '{ Terms.let[(v, s), Out](TermSyntax.when(${ r.readAs[Boolean](branch.cond) })(${ after(branch.thenp) })
        .otherwise(${ after(branch.elsep) }), "after", (p: DTerm[(v, s)]) =>
        ${ rest('{ TermSyntax._1[v, s](p)(using ${ r.spec[v](at) }) },
          env + ((key, '{ TermSyntax._2[v, s](p)(using ${ r.spec[s](at) }) }))) })(using ${ r.spec[Out](at) }) }
    case _            => r.refuse("this conditional", branch)

  private def named[Out: Type](name: String, ty: TypeRepr, value: Expr[DTerm[?]])(
      rest: Expr[DTerm[?]] => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[DTerm[Out]] = ty.asType match
    case '[x] => '{ Terms.let[x, Out](${ value.asExprOf[DTerm[x]] }, ${ Expr(name) }, (y: DTerm[x]) =>
      ${ rest('y) })(using ${ r.spec[Out](Literal(UnitConstant())) }) }

  /** The type of the state `key` (a port's variable, or its class in an `update` method's body) is bound to. */
  private def stateType(key: Symbol): TypeRepr =
    portOf(key).typeRef.memberType(r.stateOf(portOf(key), Literal(UnitConstant())))

  /** The port's class: `key` itself in an `update` method's body, else the class of the variable `key` is. */
  private def portOf(key: Symbol): Symbol = if key.isClassDef then key else key.termRef.widen.typeSymbol

  private def isUpdate(m: Symbol): Boolean = m.isDefDef && m.flags.is(Flags.Mutable)

  /** Whether `t` changes a port: it assigns a `var`, calls an `update` method, or calls a method that does. */
  private def changes(t: Term, within: Set[Symbol] = Set.empty): Boolean =
    val found = new TreeAccumulator[Boolean]:
      def foldTree(seen: Boolean, tree: Tree)(owner: Symbol): Boolean = seen || (tree match
        case Assign(_, _)                                           => true
        case a: Apply if isUpdate(a.symbol) || changing(a.symbol, within) => true
        case other                                                  => foldOverTree(seen, other)(owner))
    found.foldTree(false, t)(Symbol.spliceOwner)

  /** Whether a method of the developer's, its body kept, changes a port (`within`: the methods being asked). */
  private def changing(m: Symbol, within: Set[Symbol]): Boolean =
    !within(m) && r.isOwn(m) && r.kept(m).exists(d => changes(d.rhs.get, within + m))

private[steps] object StepReader:
  def updating[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using q: Quotes)
      : Expr[Updating[P, S, A, R]] = StepReader(Reader(q)).updating(f)

  def state[P: Type](using q: Quotes): Expr[PortState[P]] = StepReader(Reader(q)).state[P]
