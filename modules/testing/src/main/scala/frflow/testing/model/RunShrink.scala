package frflow.testing.model

import cats.Monad
import cats.syntax.all.*
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.testing.Shrinking
import frflow.core.code.Values
import frflow.core.vocab.{StateModel, Vocabulary}
import frflow.eval.Env
import frflow.testing.derive.{Always, Shrink}

/** A run that differs from its model made smaller while it still differs: a call left out, then an argument smaller,
  * then the state it starts from; each argument and state meeting what always holds of the types it holds, and the
  * state every `always(stored)` about its model.
  */
final class RunShrink(typing: Typing, always: Always, model: StateModel, v: Vocabulary):
  private val shrink = Shrink(v)

  def smallest[F[_]: Monad](differs: (Value, List[Step]) => F[Option[Difference]], s: Value, steps: List[Step],
      d: Difference): F[(Value, List[Step], Difference)] =
    (s, steps, d, Shrinking.Rounds).tailRecM { (s, steps, d, rounds) =>
      if rounds == 0 then (s, steps, d).asRight.pure[F]
      else smaller(s, steps).take(Shrinking.Tried).toList
        .collectFirstSomeM((s2, run) => differs(s2, run).map(_.map(found => (s2, run, found))))
        .map(_.fold((s, steps, d).asRight)((s2, run, found) => (s2, run, found, rounds - 1).asLeft))
    }

  private def smaller(s: Value, steps: List[Step]): LazyList[(Value, List[Step])] =
    val fewer = LazyList.from(steps.indices).map(i => steps.patch(i, Nil, 1)).filter(_.nonEmpty).map(s -> _)
    val args = LazyList.from(steps.indices).flatMap(i => argsOf(steps(i)).map(st => s -> steps.updated(i, st)))
    val states = values(s, model.state).filter(x => always.keeps(model.name, typing.literal(x, model.state)))
      .map(_ -> steps)
    fewer #::: args #::: states

  private def argsOf(st: Step): LazyList[Step] =
    LazyList.from(st.args.indices.zip(typing.params(st))).flatMap((j, ty) =>
      values(st.args(j), ty).map(v => st.copy(args = st.args.updated(j, v))))

  /** Smaller values of `ty` than `v`, each meeting what always holds of the types it holds. */
  private def values(x: Value, ty: Ty): LazyList[Value] =
    shrink.of(x, ty).take(Shrinking.Each).filter(y => always.made.forall(_.broken(List(typing.literal(y, ty)), List(ty),
      Env.of(Values.none)).isEmpty))
