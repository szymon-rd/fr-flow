package frflow
package runtime

object Bindings:
  /** What is bound where code runs: a scope's own bindings, then those of the scope it is in. Entering one costs
    * nothing for what is bound around it, so a call of a service in a large FrModel stays cheap.
    */
  private[frflow] abstract class Scope(val outer: Scope | Null):
    def own(name: String): (() => Any) | Null
    final def find(name: String): (() => Any) | Null =
      var s = this: Scope | Null
      var v: (() => Any) | Null = null
      while v == null && s != null do
        v = s.own(name)
        s = s.outer
      v
  private final class Given(bound: Map[String, () => Any], outer: Scope | Null) extends Scope(outer):
    def own(name: String): (() => Any) | Null = bound.getOrElse(name, null)

  /** One call's values (`service`): each binding read when first needed, then the same for the rest of the call. */
  private[frflow] final class Call(index: Map[String, Int], bindings: IndexedSeq[Binding], outer: Scope | Null) extends Scope(outer):
    private val cells = new Array[Cell | Null](bindings.size)
    private def cell(i: Int): Cell = cells(i) match
      case null => val c = Cell(bindings(i)); cells(i) = c; c
      case c: Cell => c
    def own(name: String): (() => Any) | Null = index.get(name).fold(null)(i => () => cell(i).get)
    def loaded(name: String): Boolean = index.get(name).exists(i => cells(i) != null && cells(i).nn.loaded)
    def value(name: String): Option[Any] = index.get(name).map(cell(_).get)

  /** A call's scope over the scope in force, for `bindings` indexed once by name (the last of a name wins). */
  private[frflow] def call(index: Map[String, Int], bindings: IndexedSeq[Binding]): Call = Call(index, bindings, current.get)
  private[frflow] def index(bindings: Seq[Binding]): Map[String, Int] = bindings.iterator.map(_.param.name).zipWithIndex.toMap

  private val current = ThreadLocal.withInitial[Scope](() => Given(Map.empty, null))
  private val reads = ThreadLocal[scala.collection.mutable.Set[String] | Null]()
  def get[A](p: Param[A]): A =
    if Building.active then
      throw IllegalStateException(s"FrFlow: ${p.name}.value is read while a model is built, so the value it has now would be " +
        s"fixed into its Lean and its running code: use ${p.name} itself as a term")
    val value = current.get.find(p.name) match
      case null => throw IllegalStateException(s"parameter ${p.name} is not bound")
      case v: (() => Any) @unchecked => v
    reads.get match
      case null => value().asInstanceOf[A]
      case seen =>
        // What the code reads itself: not what a definition or an operation's code reads in turn.
        seen += p.name
        reads.set(null)
        try value().asInstanceOf[A]
        finally reads.set(seen)

  /** A parameter as a term reads it (a definition's or a contract's formula, run): not a read of the plain code under test. */
  private[frflow] def ofTerm[A](p: Param[A]): A =
    val saved = reads.get
    reads.set(null)
    try get(p)
    finally reads.set(saved)

  /** What `body` returns, and the parameters it read itself: what a test learns of plain code it cannot see into. */
  private[frflow] def reading[T](body: => T): (T, Set[String]) =
    val saved = reads.get
    val seen = scala.collection.mutable.Set.empty[String]
    reads.set(seen)
    try (body, seen.toSet)
    finally reads.set(saved)

  def within[T](bs: Seq[Binding])(body: => T): T =
    in(Given(bs.map(b => b.param.name -> b.value).toMap, current.get))(body)

  /** Bindings named once, to enter many times (each step of a flow's run). */
  private[frflow] final class Prepared(val bound: Map[String, () => Any])
  private[frflow] def prepare(bs: Seq[Binding]): Prepared = Prepared(bs.map(b => b.param.name -> b.value).toMap)
  private[frflow] def within[T](p: Prepared)(body: => T): T = in(Given(p.bound, current.get))(body)

  private[frflow] def in[T](scope: Scope)(body: => T): T =
    val saved = current.get
    current.set(scope)
    try body
    finally current.set(saved)

  /** The bindings, each computed at most once while the bindings in force stay the ones it was computed under: for
    * terms a definition gives (pure, so the same in one world), where the world is fixed (a generated case). Under a
    * scope that binds anything again, it is computed again.
    */
  private[frflow] def oncePerScope(bs: Seq[Binding]): Seq[Binding] = bs.map { b =>
    var scope: AnyRef | Null = null
    var held: Any = null
    b.copy(value = () => {
      val now = current.get
      if !(scope eq now) then
        held = b.value()
        scope = now
      held
    })
  }
