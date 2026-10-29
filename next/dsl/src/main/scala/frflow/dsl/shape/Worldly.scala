package frflow.dsl.shape

import frflow.core.code.Code
import frflow.core.expr.Binder
import frflow.core.name.{DefName, VarId}
import frflow.core.term.{Body, Bound, Final, Sym}
import frflow.core.term.interpret.Substituted
import frflow.core.ty.Ty
import frflow.dsl.build.{AsWritten, Site}
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.run.Worlds
import frflow.dsl.vocab.{Definition, OnTheSpot, Spot}
import scala.util.control.NonFatal

/** A define whose body reads state (owner §43): it changes with the World, so it takes the world as its last input
  * (Lean: `def d (x : A) (world : World) : R`), and every call of it, in a statement or in another define, is read in
  * the world the caller holds in (`Spot.Define`'s `worldly`, `Definition.apply`). Which defines do is read off their
  * bodies: no marker.
  */
object Worldly:
  /** Whether the body on its inputs' variables reads the current world (a body that cannot be built reads none:
    * its fault is the define's, found when it is elaborated).
    */
  def reads(build: () => (List[Binder], Term[?])): Boolean =
    try Worlds.reads(build()._2.run) catch case NonFatal(_) => false

  /** The define over its inputs and the world last: its lambda, the world bound at the level after its inputs; its
    * body, one `lam` per input and one for the world.
    */
  def define[F: LeanType](name: DefName, types: List[LeanType[?]], build: () => (List[Binder], Term[?]),
      written: AsWritten): Definition[F] =
    val (xs, t) = build()
    val world = Binder(VarId.level(types.size), Worlds.binder.hint, Ty.World)
    val over: Final[Any] = [T[_]] => (s: Sym[T]) =>
      t.run(Substituted(s, Map(VarId.world -> s.free[Any](world)))).asInstanceOf[T[Any]]
    val lambda = Elab.lambda(Site.Define(name), types)(
      () => (xs :+ world, Term(over)(using t.leanType.asInstanceOf[LeanType[Any]])), written)
    val curried = (types.map(_.ty) :+ Ty.World).foldRight(t.leanType.ty)((a, r) => Ty.FnOf(List(a), r))
    Definition.onTheSpot[F](OnTheSpot(name, Code.Proven(name), lambda,
      Spot.Define(Body(name, curried, lams(xs.map(x => x.id -> x) :+ (VarId.world -> world), t)), worldly = true)))

  /** `fun x… world => body`, each input and the world bound to the variable the body was built over. */
  private def lams(bs: List[(VarId, Binder)], t: Term[?]): Final[Any] = [T[_]] => (s: Sym[T]) =>
    def over(left: List[(VarId, Binder)], env: Map[VarId, T[Any]]): T[Any] = left match
      case (id, b) :: rest =>
        s.lam[Any, Any](Bound[Any](b.hint, b.ty))(v => over(rest, env + (id -> v))).asInstanceOf[T[Any]]
      case Nil             => t.run(Substituted(s, env)).asInstanceOf[T[Any]]
    over(bs, Map.empty)
