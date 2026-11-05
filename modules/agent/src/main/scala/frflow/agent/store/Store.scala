package frflow.agent.store

/** One of the agent layer's files (its requests, its conversation), read whole and replaced whole. Interpreters: the
  * file under a lock (`FileStore`), and memory (`MemoryStore`). Laws, for both: `update(f)` stores what `f` returns
  * only on `Right`, and `load` then gives it; updates take turns, each on what the one before stored.
  */
trait Store[F[_], A]:
  def load: F[A]
  def update[E, B](f: A => Either[E, (A, B)]): F[Either[E, B]]
