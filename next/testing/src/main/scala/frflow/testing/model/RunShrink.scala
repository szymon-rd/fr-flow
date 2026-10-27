package frflow.testing.model

import cats.Monad
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.ty.Ty
import frflow.core.Theory
import frflow.core.vocab.StateModel
import frflow.eval.{Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.Made
import frflow.testing.Shrinking
import frflow.testing.derive.Shrink

/** A run that differs from its model made smaller while it still differs: a call left out, then an argument smaller,
  * then the state it starts from; each argument and state meeting what always holds of its type (and the state every
  * `always(stored)`, `fits`).
  */
final class RunShrink[S](semantics: Semantics, t: Theory, model: StateModel, fits: S => Boolean):
  private val shrink = Shrink(t.vocabulary)
  private val made = Made.of(semantics, t)

  def smallest[F[_]: Monad](differs: (S, List[Step]) => F[Option[Difference]], s: S, steps: List[Step],
      d: Difference): F[(S, List[Step], Difference)] =
    (s, steps, d, Shrinking.Rounds).tailRecM { (s, steps, d, rounds) =>
      if rounds == 0 then (s, steps, d).asRight.pure[F]
      else smaller(s, steps).take(Shrinking.Tried).toList
        .collectFirstSomeM((s2, run) => differs(s2, run).map(_.map(found => (s2, run, found))))
        .map(_.fold((s, steps, d).asRight)((s2, run, found) => (s2, run, found, rounds - 1).asLeft))
    }

  private def smaller(s: S, steps: List[Step]): LazyList[(S, List[Step])] =
    val fewer = LazyList.from(steps.indices).map(i => steps.patch(i, Nil, 1)).filter(_.nonEmpty).map(s -> _)
    val args = LazyList.from(steps.indices).flatMap(i => argsOf(steps(i)).map(st => s -> steps.updated(i, st)))
    val states = values(ScalaValue(s), model.state).map(v => Fn.as[S](v)).filter(fits).map(_ -> steps)
    fewer #::: args #::: states

  private def argsOf(st: Step): LazyList[Step] =
    val types = t.vocabulary.boundary(st.boundary).flatMap(_.ops.find(_.name == st.op)).fold(Nil)(_.params.map(_._2))
    LazyList.from(st.args.indices.zip(types)).flatMap((j, ty) =>
      values(st.args(j), ty).map(v => st.copy(args = st.args.updated(j, v))))

  /** Smaller values of `ty` than `v`, each meeting what always holds of the types it holds. */
  private def values(v: ScalaValue, ty: Ty): LazyList[ScalaValue] =
    shrink.of(semantics.reflect(v, ty), ty).take(Shrinking.Each).map(semantics.literal(_, ty))
      .filter(x => made.forall(_.broken(List(x), List(ty), Env.of(Values.none)).isEmpty))
