package frflow

/** What watches a contract's formula while its code is tested: which parts of it held (`hit`, with the branch taken),
  * and the values a `forall` or `exists` over a type ranges over (`range`, sampled; none, and it cannot run).
  */
private[frflow] trait Watch:
  def hit(t: Tree, outcome: Int): Unit
  def range(types: List[LeanType[?]]): Option[List[List[Any]]]

private[frflow] object Watch:
  private val current = ThreadLocal[Watch | Null]()
  def get: Watch | Null = current.get
  /** That a part went this way, under a test watching. */
  def hit(t: Tree, outcome: Int): Unit =
    val w = current.get
    if w != null then w.hit(t, outcome)
  def within[T](w: Watch)(body: => T): T =
    val saved = current.get
    current.set(w)
    try body
    finally current.set(saved)
