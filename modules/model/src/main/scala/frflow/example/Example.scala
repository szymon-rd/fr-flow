package frflow
package example

import frflow.testing.Table

/** A concrete case of a contract, under given parameter values: the call on `inputs` with `result`. A flow's run has the
  * world before as its last input, and the pair of its result and the world after as its result.
  */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], inputs: List[Any], result: Any, expected: Boolean):
  def call: String = s"${inputs.map(Example.show).mkString("(", ", ", ")")} ⇒ ${Example.show(result)}"
  def givens: List[String] = bindings.zip(givenSource).map { (b, src) =>
    val v = Bindings.within(bindings)(b.value())
    if Example.isData(v) then s"${b.param.name} = ${Example.show(v)}" else src
  }
  def describe: String = s"${if expected then "expect" else "reject"} $call  given ${givens.mkString(", ")}  — $note"

object Example:
  def show(v: Any): String = v match
    case s: String => "\"" + s + "\""
    case t: Table  => t.shown
    case None      => "None"
    case Some(x)   => s"Some(${show(x)})"
    case l: List[?] => l.map(show).mkString("List(", ", ", ")")
    case m: Map[?, ?] => m.map((k, x) => s"${show(k)} -> ${show(x)}").mkString("Map(", ", ", ")")
    case p: Product if p.productArity > 0 =>
      p.productPrefix + p.productIterator.map(show).mkString("(", ", ", ")")
    case other => String.valueOf(other)

  private def isData(v: Any): Boolean = v match
    case _: String | _: Boolean | _: Int | _: Long | _: BigInt | _: Char => true
    case o: Option[?] => o.forall(isData)
    case i: Iterable[?] => i.forall(isData)
    case p: Product => !p.getClass.getName.contains("$$Lambda") && p.productIterator.forall(isData)
    case _ => false

  private[frflow] object NoResult:
    override def toString: String = "no result"
