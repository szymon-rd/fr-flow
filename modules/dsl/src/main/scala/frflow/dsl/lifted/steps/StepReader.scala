package frflow.dsl.lifted.steps

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Source, WrittenAt}
import frflow.dsl.lifted.{LiftOps, Lifted, Lifting, Reader}
import frflow.dsl.term.{Lift, Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** Scala that changes a port, read into state passing, as Aeneas reads Rust's `&mut`: the port's variable stands for
  * the state of its store; a call of an `update` method is the state its body leaves; what follows a change reads
  * the new state; a conditional that changes the state gives the state either branch leaves. What changes nothing
  * is read by the reader of lifted code (`r`). Read among other calls (`others` given), each call of the store is a
  * step: before it the others may have left another state (`StepCalls.interfered`), and what it did is kept in a
  * trace. Sound because the port is the code's alone, which Scala's separation checking checks where the code is
  * compiled, and each of the store's methods is one step of the world, which the developer assumes of the store.
  */
private[steps] final class StepReader(val r: Reader, val others: Option[Expr[Any]], val ofStore: Boolean)
    extends StepCalls, StepWalk:
  import r.q.reflect.*

  def updating[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using Quotes)
      : Expr[Lifted.Of2[S, A, (R, S)]] =
    val (p, a, code) = lambda(f)
    val steps = '{ (state: DTerm[S], x: DTerm[A]) => ${
      run[(R, S)](code, TypeRepr.of[R], p.symbol)((v, w) => packed(v, TypeRepr.of[R], p.symbol)(using w)
        .asExprOf[DTerm[(R, S)]])(using Walk(r.Env.of((p.symbol, 'state), (a.symbol, 'x)), 0, None, false)) } }
    '{ Lifted.Of2(Lifting.two[S, A, (R, S)](DefName(${ Expr(r.defining.name) }), WrittenAt.in(Source.path(
      ${ Expr(file) })), ${ written(f, List(stateName[P](p), a.name)) })($steps)(using ${ r.spec[S](p) },
      ${ r.spec[A](a) }, ${ r.spec[(R, S)](code) }), (before: S, x: A) => ${ pure[P, S, A, R](f, 'before, 'x) }) }

  def interleaving[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using Quotes)
      : Expr[Defined[(S, Map[BigInt, S], A) => (R, List[(S, S)])]] =
    val (p, a, code) = lambda(f)
    val steps = '{ (state: DTerm[S], between: DTerm[Map[BigInt, S]], x: DTerm[A]) => ${
      val start = r.Env.of((p.symbol, 'state), (a.symbol, 'x), (trace, '{ LiftOps.nil[(S, S)](using
        ${ r.spec[(S, S)](p) }) }))
      run[(R, List[(S, S)])](code, TypeRepr.of[R], p.symbol)((v, w) => '{ LiftOps.pair[R, List[(S, S)]](
        ${ v.asExprOf[DTerm[R]] }, ${ w.env(trace).asExprOf[DTerm[List[(S, S)]]] })(using
        ${ r.spec[(R, List[(S, S)])](code) }) })(using Walk(start, 0, Some(('between, 'x)), false)) } }
    '{ Lifting.three[S, Map[BigInt, S], A, (R, List[(S, S)])](DefName(${ Expr(r.defining.name) }),
      WrittenAt.in(Source.path(${ Expr(file) })), ${ written(f, List(stateName[P](p), "between", a.name)) })(
      $steps)(using ${ r.spec[S](p) }, ${ r.spec[Map[BigInt, S]](p) }, ${ r.spec[A](a) },
      ${ r.spec[(R, List[(S, S)])](code) }) }

  /** The type of a port's state, as the witness the compiler finds for the port (`PortState.derived`). */
  def state[P: Type](using Quotes): Expr[PortState[P]] =
    r.stateType(TypeRepr.of[P], Literal(UnitConstant())).asType match
      case '[s] => '{ new PortState[P] { type S = s } }

  private def file: String = Source.relative(Position.ofMacroExpansion.sourceFile.path)

  private def lambda(f: Expr[Any]): (ValDef, ValDef, Term) = r.bare(f.asTerm) match
    case Lambda(List(p, a), code) => (p, a, code)
    case other                    => r.refuse("a function that is not a lambda of a port and an input", other)

  /** The code as written, its inputs named as the model's are: the store's state by the store's `var`. */
  private def written(f: Expr[Any], names: List[String])(using Quotes): Expr[AsWritten] =
    '{ AsWritten(Source.of($f).text, ${ Expr(names) }) }

  private def stateName[P: Type](at: Tree): String =
    def of(port: TypeRepr): String =
      val state = r.stateOf(port.typeSymbol, at)
      if r.isStore(port) then state.name else of(port.memberType(state))
    of(TypeRepr.of[P])

  /** The Scala run on a port made from a state: its result, with the store's state after it. */
  private def pure[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R], before: Expr[S], a: Expr[A])(
      using Quotes): Expr[(R, S)] =
    def made(port: TypeRepr, store: Term): Term =
      val under = port.memberType(r.stateOf(port.typeSymbol, f.asTerm))
      if r.isStore(port) then store
      else Apply(Select(New(Inferred(port)), port.typeSymbol.primaryConstructor), List(made(under, store)))
    def storeOf(port: TypeRepr): TypeRepr =
      if r.isStore(port) then port else storeOf(port.memberType(r.stateOf(port.typeSymbol, f.asTerm)))
    val kind = storeOf(TypeRepr.of[P])
    val fresh = Apply(Select(New(Inferred(kind)), kind.typeSymbol.primaryConstructor), List(before.asTerm))
    ValDef.let(Symbol.spliceOwner, "store", fresh)(store =>
      '{ val out = $f(${ made(TypeRepr.of[P], store).asExprOf[P] }, $a)
         (out, ${ Select(store, r.stateOf(kind.typeSymbol, f.asTerm)).asExprOf[S] }) }.asTerm).asExprOf[(R, S)]

  /** `t` run from the state `key` is bound to: its value and where the reading is after it, given to the rest. */
  def run[Out: Type](t: Term, as: TypeRepr, key: Symbol)(rest: Rest[Out])(using walk: Walk)(using Quotes)
      : Expr[DTerm[Out]] = r.bare(t) match
    case pure if quiet(pure)                             => rest(r.read(pure, as)(using walk.env), walk)
    case Block(Nil, e)                                   => run(e, as, key)(rest)
    case Block((v @ ValDef(_, tpt, Some(rhs))) :: ss, e) => run(rhs, tpt.tpe.widen, key)((x, after) =>
      named[Out](v.name, tpt.tpe.widen, x)(y => run(Block(ss, e), as, key)(rest)(using after.bound(v.symbol, y))))
    case Block((s: Term) :: ss, e)                       =>
      run(s, s.tpe.widen, key)((_, after) => run(Block(ss, e), as, key)(rest)(using after))
    case Assign(to, value) if to.symbol == r.stateOf(portOf(key), t) => assigned(value, to, key)(rest)
    case branch @ If(c, _, _) if quiet(c)                => either(branch, as, key)(rest)
    case call if storeCall(call)                         => step(call, as, key)(rest)
    case call if serviceCall(call)                       => called(call, key)(rest)
    case other                                           => r.refuse("a use of a port here: a port is used in a " +
      "statement of its own (`val x = port.call(…)`), an `if`'s branch, or an `update` method's body", other)

  /** The state a `var`'s assignment leaves: the value assigned, named for what follows. */
  private def assigned[Out: Type](value: Term, to: Term, key: Symbol)(rest: Rest[Out])(using Walk)(using Quotes)
      : Expr[DTerm[Out]] = run(value, to.tpe.widen, key)((x, after) =>
    named[Out](to.symbol.name, to.tpe.widen, x)(y => rest('{ Lift.constant[Unit](()) }, after.bound(key, y))))

  /** A conditional that changes the state: its value with what either branch leaves, named for what follows. */
  private def either[Out: Type](branch: If, as: TypeRepr, key: Symbol)(rest: Rest[Out])(using walk: Walk)(
      using Quotes): Expr[DTerm[Out]] = packedType(as, key).asType match
    case '[j] =>
      def side(t: Term): Expr[DTerm[j]] = run[j](t, as, key)((x, w) => packed(x, as, key)(using w)
        .asExprOf[DTerm[j]])
      val steps = walk.step + count(branch.thenp).max(count(branch.elsep))
      '{ Terms.let[j, Out](TermSyntax.when(${ r.readAs[Boolean](branch.cond)(using walk.env) })(
        ${ side(branch.thenp) }).otherwise(${ side(branch.elsep) }), "after", (p: DTerm[j]) =>
        ${ val (v, carried) = unpacked('p, as, key)
           rest(v, walk.copy(env = walk.env ++ carried, step = steps)) })(using ${ r.spec[Out](branch) }) }

  def named[Out: Type](name: String, ty: TypeRepr, value: Expr[DTerm[?]])(
      rest: Expr[DTerm[?]] => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[DTerm[Out]] = ty.asType match
    case '[x] => '{ Terms.let[x, Out](${ value.asExprOf[DTerm[x]] }, ${ Expr(name) }, (y: DTerm[x]) =>
      ${ rest('y) })(using ${ r.spec[Out](Literal(UnitConstant())) }) }

private[steps] object StepReader:
  def updating[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R])(using q: Quotes)
      : Expr[Lifted.Of2[S, A, (R, S)]] = of[P](None).updating(f)

  def interleaving[P: Type, S: Type, A: Type, R: Type](f: Expr[(P, A) => R],
      others: Expr[Lifted.Of3[A, S, S, Boolean]])(using q: Quotes)
      : Expr[Defined[(S, Map[BigInt, S], A) => (R, List[(S, S)])]] =
    of[P](Some(others)).interleaving(f)

  def state[P: Type](using q: Quotes): Expr[PortState[P]] = of[P](None).state[P]

  /** The reader of code over the port `P`: a store's own code, or a service's. */
  private def of[P: Type](others: Option[Expr[Any]])(using q: Quotes): StepReader =
    val r = Reader(q)
    StepReader(r, others, r.isStore(r.q.reflect.TypeRepr.of[P]))
