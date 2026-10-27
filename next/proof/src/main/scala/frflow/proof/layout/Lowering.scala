package frflow.proof.layout

import frflow.core.analysis.{Guards, Resolved}
import frflow.core.name.{KbName, NodeId}
import frflow.core.term.interpret.Guard
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, LowerProp, Naming}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.terms.TermTable

/** How one FrModel's Lean is lowered, computed once for every module: its environment (each model's field of
  * the world is its boundary's name, each model's namespace its name capitalized), the names a binder may not take
  * (every symbol, every domain type, `World`), what always holds, and the lowering of propositions. `canonical`
  * names every variable by the order it is bound (`Naming`): the lowering a node's content prints its meaning with.
  */
final class Lowering(val resolved: Resolved, val table: TermTable, canonical: Boolean = false):
  private val v = resolved.theory.vocabulary
  val kb: KbName = resolved.theory.name
  val layout: Layout = Layout(kb)
  val env: LowerEnv = LowerEnv(kb, d => table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value))),
    m => Names.ident(v.model(m).fold(m.value)(_.boundary.value)),
    b => Names.builtin(v.boundary(b).fold(b.value)(_.className)), v.dataType, m => v.model(m).map(_.state),
    v.symbols.flatMap(s => s.ty match
      case SymbolType.Typed(t) => Ty.errorOf(t).map(s.name -> _)
      case _                   => None).toMap,
    v.boundaries.exists(_.fails.nonEmpty), v.models.map(m => Names.ident(m.boundary.value)))
  val naming: Naming = Naming.over(v.symbols.map(_.name.value).toSet,
    (v.types.map(_.typeName.value) ++ v.sorts.map(_.name.value) :+ "World").toSet).copy(canonical = canonical)
  val guards: List[Guard] = Guards.of(resolved.theory)
  val props: LowerProp = LowerProp(table, env)

  def node(n: NodeId): Boolean = resolved.theory.node(n).nonEmpty
  def isDefine(name: String): Boolean = v.defines.exists(_.name.value == name)
  def isModelSpace(name: String): Boolean = v.models.exists(_.name.value.capitalize == name)
  def isBoundaryClass(name: String): Boolean = v.boundaries.exists(_.className == name)
