package frflow.executions.latch

import java.util.concurrent.atomic.AtomicBoolean

/** A door that closes once: code read from its TASTy for the tests, as any code is. */
final class Latch:
  private val closed = new AtomicBoolean(false)

  def close(): Unit = closed.set(true)

  def enter(): Unit =
    if closed.get() then throw new IllegalStateException("closed")
