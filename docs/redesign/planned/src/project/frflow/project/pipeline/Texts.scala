package frflow.project.pipeline

import frflow.core.analysis.{Fixed, Resolve, Resolved}
import frflow.core.code.RunCheck
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.Statement
import frflow.core.Theory

/** The content fields whose texts are today's renderings of values (`Example.describe`, `Types` Scala text, the
  * boundary model's Lean, `CodeProof`'s prefixes, `RunCheck.describe`), byte for byte: each pinned per node by the
  * step-0 golden.
  */
object Texts:
  def examples(s: Statement): List[String] = ???
  /** `name: means` of every opaque type and symbol the node speaks of, sorted: what its statement mentions (through
    * its defines), its operation, the terms it defines, and the opaque types of the rules of the invariants it keeps
    * (today's `termsOf(n) ++ n.defines`).
    */
  def vocabulary(t: Theory, id: NodeId): List[String] =
    val v = t.vocabulary
    val m = Resolve.mentions(t, id)
    val defined = t.node(id).toList.flatMap(n => Fixed.of(n.statement))
    val kept = t.edges.collect { case Edge.Keeps(`id`, i, _) => Resolve.mentions(t, i).types }.flatten
    val sorts = (m.types ++ kept ++ defined.collect { case Fixed.Sort(s) => s }).toSet
    val op = t.node(id).flatMap(_.statement.operation)
    val symbols = (m.symbols ++ op ++ defined.collect { case Fixed.Term(s) => s }).toSet
    (v.sorts.filter(s => sorts(s.name)).map(s => s"${s.name.value}: ${s.means}") ++
      v.symbols.filter(s => symbols(s.name)).map(s => s"${s.name.value}: ${s.means}")).sorted

  def keeps(r: Resolved, id: NodeId): List[String] = ???
  def uses(r: Resolved, id: NodeId): List[String] = ???
  def implementation(r: Resolved, id: NodeId): Option[String] = ???
  def model(r: Resolved, id: NodeId): Option[List[String]] = ???
  def implementations(r: Resolved, id: NodeId): Option[List[String]] = ???
  def runCheck(c: RunCheck): String = ???
