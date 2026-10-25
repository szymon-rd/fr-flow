package frflow
package runtime

import java.util.concurrent.atomic.AtomicBoolean
import scala.collection.concurrent.TrieMap

/** A parameter's value for one call, read when first needed; a function it holds answers each question once. */
private[frflow] final class Cell(val binding: Binding):
  private val read = AtomicBoolean(false)
  lazy val get: Any =
    val v = Cell.memoized(binding.value())
    read.set(true)
    v
  def loaded: Boolean = read.get

private[frflow] object Cell:
  private def lambda(f: AnyRef) = f.getClass.getName.contains("Lambda")

  private def memo(f: Any => Any): Any => Any =
    val seen = TrieMap.empty[Any, Any]
    a => seen.getOrElseUpdate(a, f(a))

  def memoized(v: Any): Any = v match
    case f: Function1[?, ?] if lambda(f) => memo(f.asInstanceOf[Any => Any])
    // A function of more arguments answers each list of them once.
    case f: AnyRef if lambda(f) && Fn.arity(f).exists(_ >= 2) =>
      val m = memo(args => Fn.call(f, args.asInstanceOf[List[Any]]))
      Fn.of(Fn.arity(f).get)(m)
    case other => other
