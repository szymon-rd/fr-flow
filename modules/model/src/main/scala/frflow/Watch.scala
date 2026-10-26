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
  /** A `forall` or `exists` over numbers ranging over the values' own numbers, their neighbours and 0: a claim of
    * order over them (a moment between a start and an end) holds of all numbers when it holds of those. Over other
    * types, `others` (none: it cannot run).
    */
  def overNumbers(values: List[Any], others: List[LeanType[?]] => Option[List[List[Any]]] = _ => None): Watch =
    new Watch:
      private val ns = (BigInt(0) :: values.flatMap(numbers)).distinct
      def hit(t: Tree, outcome: Int): Unit = ()
      def range(ts: List[LeanType[?]]): Option[List[List[Any]]] =
        if ts.forall(t => Types.scala(t) == "BigInt") then
          Some(ts.foldRight(List(List.empty[Any]))((_, rows) => for n <- ns; r <- rows yield n :: r))
        else others(ts)
  private def numbers(v: Any): List[BigInt] = v match
    case b: BigInt       => List(b - 1, b, b + 1)
    case xs: Iterable[?] => xs.toList.flatMap(numbers)
    case p: Product      => p.productIterator.toList.flatMap(numbers)
    case _               => Nil

  def within[T](w: Watch)(body: => T): T =
    val saved = current.get
    current.set(w)
    try body
    finally current.set(saved)
