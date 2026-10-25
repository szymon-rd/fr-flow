package frflow
package testing

/** A function a test made up: a table of answers, and its answer elsewhere. What a function-typed parameter
  * (`sessions: String => Option[UserId]`) is generated as.
  */
sealed trait Table:
  def entries: List[(List[Any], Any)]
  def default: Any
  protected def at(args: List[Any]): Any = entries.find(_._1 == args).fold(default)(_._2)
  def shown: String =
    val es = entries.map((k, v) => s"${k.map(Example.show).mkString(", ")} ↦ ${Example.show(v)}")
    (es :+ s"else ${Example.show(default)}").mkString("{", ", ", "}")

private[frflow] object Table:
  /** The most arguments a generated function takes. */
  val MaxArity = 6
  def apply(arity: Int, entries: List[(List[Any], Any)], default: Any): Table = arity match
    case 1 => Table1(entries, default)
    case 2 => Table2(entries, default)
    case 3 => Table3(entries, default)
    case 4 => Table4(entries, default)
    case 5 => Table5(entries, default)
    case 6 => Table6(entries, default)
    case n => throw CannotGenerate(s"a function of $n arguments")

  private[frflow] final case class Table1(entries: List[(List[Any], Any)], default: Any) extends Table with (Any => Any):
    def apply(a: Any): Any = at(List(a))
    override def toString: String = shown
  private[frflow] final case class Table2(entries: List[(List[Any], Any)], default: Any) extends Table with ((Any, Any) => Any):
    def apply(a: Any, b: Any): Any = at(List(a, b))
    override def toString: String = shown
  private[frflow] final case class Table3(entries: List[(List[Any], Any)], default: Any) extends Table with ((Any, Any, Any) => Any):
    def apply(a: Any, b: Any, c: Any): Any = at(List(a, b, c))
    override def toString: String = shown
  private[frflow] final case class Table4(entries: List[(List[Any], Any)], default: Any) extends Table
      with ((Any, Any, Any, Any) => Any):
    def apply(a: Any, b: Any, c: Any, d: Any): Any = at(List(a, b, c, d))
    override def toString: String = shown
  private[frflow] final case class Table5(entries: List[(List[Any], Any)], default: Any) extends Table
      with ((Any, Any, Any, Any, Any) => Any):
    def apply(a: Any, b: Any, c: Any, d: Any, e: Any): Any = at(List(a, b, c, d, e))
    override def toString: String = shown
  private[frflow] final case class Table6(entries: List[(List[Any], Any)], default: Any) extends Table
      with ((Any, Any, Any, Any, Any, Any) => Any):
    def apply(a: Any, b: Any, c: Any, d: Any, e: Any, f: Any): Any = at(List(a, b, c, d, e, f))
    override def toString: String = shown
