package frflow.eval.flow

import cats.effect.{IO, Ref}
import frflow.*
import frflow.dsl.flow.Terms

/** A model's state held in a `Ref`, as a program running in production reads and writes it: what the models'
  * instances (`Kept`, `Ticks`) run on under `Running`.
  */
final class Held[S: LeanType](state: Ref[IO, S], terms: Terms) extends Model[IO, S]:
  def get: IO[Term[S]] = state.get.map(terms.term(_))
  def set(s: Term[S]): IO[Unit] = IO.defer(state.set(terms.value(s)))
