package frflow.vocab

import frflow.core.term.{Bound, Ext}
import frflow.eval.term.{Evaluate, Run}
import java.util.concurrent.atomic.AtomicInteger

/** The evaluator extended with `count` outside the core: it counts in Scala, says so for `Count`'s key (matched on
  * the key's type: `E` is `Count`, no cast), and says how often it counted.
  */
final class Counting extends Evaluate, Count[Run]:
  val calls = AtomicInteger(0)
  override def extension[E[_[_]]](key: Ext[E]): Option[E[Run]] = key match
    case _: Count.type => Some(this)
    case _             => None
  def count[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[BigInt] =
    val kept = filter(xs, x)(p)
    env => { calls.incrementAndGet(); kept(env).map(k => BigInt(k.size)) }
