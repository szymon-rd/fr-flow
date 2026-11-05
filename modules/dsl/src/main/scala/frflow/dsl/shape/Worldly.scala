package frflow.dsl.shape

import cats.syntax.all.*
import frflow.core.code.Code
import frflow.core.expr.{Binder, Expr, Exprs}
import frflow.core.name.{DefName, VarId}
import frflow.core.term.Bound
import frflow.core.term.interpret.Substituted
import frflow.core.term.language.{Body, Final, Sym}
import frflow.core.ty.Ty
import frflow.dsl.build.{AsWritten, Fault, Site}
import frflow.dsl.build.Failure
import frflow.dsl.run.Worlds
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, OnTheSpot, Spot}

/** A define whose body reads state (owner §43): it changes with the World, so it takes the world as its last input
  * (Lean: `def d (x : A) (world : World) : R`), and every call of it, in a statement or in another define, is read in
  * the world the caller holds in (`Spot.Define`'s `worldly`, `Definition.apply`). Which defines do is read off their
  * bodies: no marker.
  */
object Worldly:
  /** Whether the body on its inputs' variables reads the current world. A body that cannot be built (its fault, a
    * `Failure`, is found again when the define is elaborated, and placed there) is read as it is written, reading none.
    */
  def reads(build: () => (List[Binder], Term[?])): Boolean =
    Either.catchOnly[Failure](build()._2).toOption.flatMap(Worlds.reads).contains(true)

  /** The define over its inputs and the world last: its lambda, the world bound at the level after its inputs; its
    * body, one `lam` per input and one for the world.
    */
  def define[F: LeanType](name: DefName, types: List[LeanType[?]], build: () => (List[Binder], Term[?]),
      written: AsWritten): Definition[F] =
    val (xs, t) = build()
    val world = Binder(VarId.level(types.size), Worlds.binder.hint, Ty.World)
    val over: Final[Any] = [T[_]] => (s: Sym[T]) =>
      t.run(Substituted(s, Worlds.as(s.free[Any](world)))).asInstanceOf[T[Any]]
    val lambda = Elab.lambda(Site.Define(name), types)(() => (xs :+ world, unconstant(Term(over)(
      using t.leanType.asInstanceOf[LeanType[Any]]))), written)
    val curried = (types.map(_.ty) :+ Ty.World).foldRight(t.leanType.ty)((a, r) => Ty.FnOf(List(a), r))
    Definition.onTheSpot[F](OnTheSpot(name, Code.Proven(name), lambda,
      Spot.Define(Body(name, curried, lams(xs, world, t)), worldly = true)))

  /** A define's body is a value, which no step changes or keeps: `isConstant` is a statement's (owner §45 A). */
  private def unconstant[A](t: Term[A]): Term[A] =
    if Term.exprOf(t).exists(e => Exprs.all(e).exists {
        case Expr.Constant(_, _, _) => true
        case _                      => false
      }) then throw Failure(Fault.ConstantInside("in a define"))
    else t

  /** `fun x… world => body`, each input and the world bound to the variable the body was built over. */
  private def lams(xs: List[Binder], world: Binder, t: Term[?]): Final[Any] = [T[_]] => (s: Sym[T]) =>
    def over(left: List[Binder], env: Map[Binder, T[Any]]): T[Any] = left match
      case b :: rest =>
        s.lam[Any, Any](Bound[Any](b.hint, b.ty))(v => over(rest, env + (b -> v))).asInstanceOf[T[Any]]
      case Nil       => s.lam[Any, Any](Bound[Any](world.hint, world.ty))(w =>
          t.run(Substituted(s, env ++ Worlds.as(w))).asInstanceOf[T[Any]]).asInstanceOf[T[Any]]
    over(xs, Map.empty)
