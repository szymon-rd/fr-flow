package frflow.proof.layout

import frflow.core.analysis.outside.{Guards, Reads}
import frflow.core.analysis.Reserved
import frflow.core.analysis.resolution.Resolved
import frflow.core.code.Code
import frflow.core.name.{KbName, NodeId, SymbolName}
import frflow.core.spec.Range
import frflow.core.term.interpret.Guard
import frflow.core.term.language.Sym
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.lean.ast.{LExpr, Names}
import frflow.proof.lean.lower.{LowerEnv, LowerProp, Naming}
import frflow.proof.lean.term.Printed
import frflow.proof.terms.TermTable

/** How one FrModel is lowered, computed once for every module: its environment, the names a binder may not take
  * (every symbol, every domain type), what always holds of what each statement is about, and the lowering of
  * propositions. `canonical` names every variable by the order it is bound (`Naming`): the lowering a node's content
  * prints its meaning with.
  */
final class Lowering(val resolved: Resolved, val table: TermTable, canonical: Boolean = false):
  private val v = resolved.theory.vocabulary
  val kb: KbName = resolved.theory.name
  val layout: Layout = Layout(kb)
  /** The defines a rule calls, and those of them lowered twice (`RuleSide`). */
  val ruleSide: RuleSide = RuleSide.of(resolved)
  val env: LowerEnv = LowerEnv(kb,
    d => table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value))), v.dataType, ruleSide.twice)

  /** A variable takes no name a symbol, the FrModel's namespace or a name the generated files write themselves
    * (`Reserved`) prints as, and no domain type's.
    */
  val naming: Naming = Naming.over(v.symbols.map(_.name.value).toSet ++ Reserved.names + kb.value,
    (v.types.map(_.typeName.value) ++ v.sorts.map(_.name.value)).toSet).copy(canonical = canonical)

  /** What always holds that a statement takes. */
  val guards: List[Guard] = Guards.of(resolved.theory)

  /** The values provided where the code runs a statement mentions: what always holds of each is a hypothesis. */
  def provided(n: NodeId): List[(SymbolName, Ty)] = Reads.provided(resolved.theory, n)
  val props: LowerProp = LowerProp(table, env, naming, LowerProp.Values(fromOutside,
    s => resolved.theory.code.attached.get(s).exists(a => a.code.proven.nonEmpty || (a.code match
      case Code.Valued(_) | Code.Provided => true
      case _                              => false))))

  def node(n: NodeId): Boolean = resolved.theory.node(n).nonEmpty
  def isDefine(name: String): Boolean = v.defines.exists(d => d.name.value == name ||
    ruleSide.twice(d.name) && LowerEnv.guarded(d.name).value == name)

  /** What always holds of a value provided where the code runs, at its symbol: a value from outside (owner §21). */
  private def fromOutside(s: SymbolName): List[LExpr] =
    val t = resolved.theory
    val provided = t.code.attached.get(s).exists(_.code == Code.Provided)
    v.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) if provided => ty }.toList.flatMap(ty =>
      Guards.byAlways(t).filter((n, _) => t.node(n).flatMap(_.statement.range).exists {
        case Range.Made(u) => Guards.applies(t, u, ty)
        case _             => false
      }).map((_, g) => Printed.formula(env, naming)([T[_]] => (sym: Sym[T]) =>
        g.of[T, Any](ty, sym).fold(sym.bool(true))(_(sym.param[Any](s, ty))))))
