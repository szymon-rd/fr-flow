package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.code.Code
import frflow.core.name.{KbName, NodeId, SymbolName}
import frflow.core.spec.Range
import frflow.core.term.Sym
import frflow.core.term.interpret.Guard
import frflow.proof.lean.ast.{LExpr, Names}
import frflow.proof.lean.term.Printed
import frflow.proof.lean.lower.{LowerEnv, LowerModels, LowerProp, Naming}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.terms.TermTable
import frflow.core.analysis.outside.{Guards, Reads}

/** How one FrModel's Lean is lowered, computed once for every module: its environment (each model's field of the world
  * is its name, each model's namespace its name capitalized, its class `Space.Ops`), the names a binder may not take
  * (every symbol, every domain type, `World`), what always holds of what each statement is about, and the lowering of
  * propositions. `canonical` names every variable by the order it is bound (`Naming`): the lowering a node's content
  * prints its meaning with.
  */
final class Lowering(val resolved: Resolved, val table: TermTable, canonical: Boolean = false):
  private val v = resolved.theory.vocabulary
  val kb: KbName = resolved.theory.name
  val layout: Layout = Layout(kb)
  val env: LowerEnv = LowerEnv(kb, d => table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value))),
    m => Names.ident(m.value),
    op => LExpr.Const(v.modelOf(op).fold(List(Names.builtin(op.value)))(m =>
      List(LowerModels.className(m), Names.ident(op.value)))),
    v.dataType, m => v.model(m).map(_.state),
    v.symbols.flatMap(s => s.ty match
      case SymbolType.Typed(t) => Ty.errorOf(t).map(s.name -> _)
      case _                   => None).toMap,
    v.models.exists(_.fails.nonEmpty), v.models.map(m => Names.ident(m.name.value)))
  val naming: Naming = Naming.over(v.symbols.map(_.name.value).toSet,
    (v.types.map(_.typeName.value) ++ v.sorts.map(_.name.value) :+ "World").toSet).copy(canonical = canonical)
  /** What always holds that a statement takes: on a world, the rules of the stores it reads only (owner §33). */
  def guards(n: NodeId): List[Guard] = Guards.of(resolved.theory, n)
  /** The values provided where the code runs a statement mentions: what always holds of each is a hypothesis. */
  def provided(n: NodeId): List[(SymbolName, Ty)] = Reads.provided(resolved.theory, n)
  val props: LowerProp = LowerProp(table, env, fromOutside, s => resolved.theory.code.attached.get(s).exists(a =>
    a.code.proven.nonEmpty || (a.code match
      case Code.Valued(_) | Code.Modelled(_) | Code.Provided => true
      case _                                 => false)))

  def node(n: NodeId): Boolean = resolved.theory.node(n).nonEmpty
  def isDefine(name: String): Boolean = v.defines.exists(_.name.value == name)
  def isModelSpace(name: String): Boolean = v.models.exists(_.name.value.capitalize == name)
  def isModelClass(name: String): Boolean = v.models.exists(LowerModels.className(_).text == name)

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
