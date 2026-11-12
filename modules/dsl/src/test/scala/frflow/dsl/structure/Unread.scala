package frflow.dsl.structure

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import scala.annotation.experimental

/** A class the reader does not read: a member with a loop. */
@experimental object Unread:
  /** A counter. */
  trait Counter extends Mutable:
    /** Counts up to a number: where it then stands. */
    update def upTo(n: BigInt): BigInt

  final class Looping(var at: BigInt) extends Counter:
    update def upTo(n: BigInt): BigInt =
      while at < n do at = at + BigInt(1)
      at
