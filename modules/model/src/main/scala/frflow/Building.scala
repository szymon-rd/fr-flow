package frflow

/** While a term, a define, a flow or a model's operation is built (once, on symbolic values): a parameter's value read
  * then would become a constant in both its Lean and its Scala, so `Bindings.get` refuses it.
  */
private[frflow] object Building:
  private val depth = ThreadLocal.withInitial[Int](() => 0)
  def apply[T](body: => T): T =
    depth.set(depth.get + 1)
    try body
    finally depth.set(depth.get - 1)
  def active: Boolean = depth.get > 0
