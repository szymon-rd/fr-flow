package frflow.testing.derive

/** Where one case's draws are: the values it has drawn (`Pool`), and its random stream. */
final case class Draws(pool: Pool, stream: Stream):
  /** The stream moved on, and a stream of its own for a try that may be thrown away. */
  def fork: (Draws, Draws) =
    val (after, n) = stream.next
    (copy(stream = after), copy(stream = Stream(n)))
