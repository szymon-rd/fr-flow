package frflow.project.rocq

import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger, AtomicReference}

/** A gate, read from its TASTy by `GateRocqSuite`: code for the rules of `docs/THREADS-GENERATOR.md` that Ox's
  * scopes and forks do not come to, and for what is refused. It is never run.
  */
final class Gate:
  private val open = new AtomicBoolean(false)
  private val passed = new AtomicInteger(0)
  private val next = new AtomicReference[Gate](null)

  /** A `var` through a `while` whose condition is an effect. */
  def drain(): Int =
    var left = 0
    while open.getAndSet(false) do left = passed.decrementAndGet()
    left

  /** Two effects among the arguments of one call. */
  def swap(): Boolean = both(open.getAndSet(false), open.get())

  private def both(a: Boolean, b: Boolean): Boolean = a && b

  /** A value that may be null, read after another effect: `unnull` where it is read. */
  def after(): Boolean =
    val gate = next.get()
    open.set(true)
    gate.swap()

  /** A return that ends a branch early; a value dropped. */
  def admit(): Boolean =
    if !open.get() then return false
    val _ = passed.incrementAndGet()
    true

  /** Not read: a method of a class no table has. */
  def stamp(): Int = System.identityHashCode(this)

  /** Not read, and with no definition: a result of a type that is not read. */
  def name(): String = Thread.currentThread().getName

  /** Not read: a variable named as the library names a program. */
  def shadow(call: Boolean): Boolean = call

  /** Not read: a return that does not end its method. */
  def twice(): Int =
    while open.get() do return 1
    2
