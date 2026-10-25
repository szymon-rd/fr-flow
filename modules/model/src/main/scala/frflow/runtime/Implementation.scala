package frflow
package runtime

import frflow.types.Shape

/** The code registered for a contract's operation: `wiring` is its source; `proven`, the `define` Lean proves. */
final case class Implementation(contract: String, factory: () => Any, files: List[String], wiring: String = "", proven: Option[Def[?]] = None,
    flowDef: Option[Def[?]] = None, calls: List[String] = Nil):
  /** Proven code that is a flow: `proven` is its run on the models, `flowDef` the flow itself. */
  def flow: Boolean = flowDef.isDefined
  /** The running code is the proven `define` itself, not code checked against it (`runs`). */
  def provenCode: Boolean = proven.isDefined && wiring.isEmpty
  // The last of `files` is the model's file, where it is attached.
  def sources: List[String] = files.dropRight(1)
  def modelFile: Option[String] = files.lastOption

object Implementation:
  private val Ident = "[A-Za-z_][A-Za-z0-9_]*".r
  /** A flow attached as a contract's code: `impl` takes the flow's inputs as terms and gives its steps. */
  def ofFlow(contract: Node[?], impl: AnyRef, text: String, files: List[String]): Implementation =
    val (ins, r) = Node.flowTypes(contract.op.getOrElse(throw IllegalArgumentException(s"${contract.id} is not a contract")))
    val name = if Ident.matches(text) then text else contract.id.head.toLower.toString + contract.id.tail
    val flow = Def(Lifted.flow(impl, ins, text), r, Some(name), isFlow = true)
    val pair = LeanType.of[Any](Shape.TupleOf(List(r, summon[LeanType[World]])))
    val code = Def(Lifted.runOn(flow, ins, pair, contract.failure.map(_.err)), pair, Some(s"${name}_run"))
    Implementation(contract.id, () => code.lifted.value, files, "", Some(code), Some(flow))
