package frflow.eval.flow

import frflow.*

/** The shelf's model: the numbers put on it, oldest first. */
final class Kept[F[_]: Flow](state: Model[F, List[BigInt]]) extends Shelf[F, Term]:
  def items: F[Term[List[BigInt]]] = state.get
  def put(n: Term[BigInt]): F[Unit] = state.get.flatMap(held => state.set(held :+ n))
