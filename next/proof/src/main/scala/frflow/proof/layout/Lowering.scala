package frflow.proof.layout

import frflow.core.analysis.{Reserved, Resolved}
import frflow.core.code.Code
import frflow.core.expr.Prog
import frflow.core.name.{KbName, ModelName, NodeId, SymbolName}
import frflow.core.spec.Range
import frflow.core.term.Sym
import frflow.core.term.interpret.Guard
import frflow.proof.lean.ast.{LBinder, LExpr, LOp, Names}
import frflow.proof.lean.term.Printed
import frflow.proof.lean.lower.{Atoms, LowerEnv, LowerModels, LowerFaults, LowerProp, Naming}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.terms.TermTable
import frflow.core.analysis.outside.{Guards, Outsides, Reads}

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
  /** The defines a rule calls, and those of them lowered twice (`RuleSide`). */
  val ruleSide: RuleSide = RuleSide.of(resolved)
  private val unclocked: LowerEnv = LowerEnv(kb,
    d => table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value))),
    m => Names.ident(m.value),
    op => if op == Prog.leftWins then LowerFaults.leftWins else if op == Prog.reach then LowerFaults.reach
      else LExpr.Const(v.modelOf(op).fold(
      List(Names.builtin(op.value)))(m => List(LowerModels.className(m), Names.ident(op.value)))),
    v.dataType, m => v.model(m).map(_.state),
    v.symbols.flatMap(s => s.ty match
      case SymbolType.Typed(t) => Ty.errorOf(t).map(s.name -> _)
      case _                   => None).toMap,
    v.models.exists(_.fails.nonEmpty), v.models.map(m => Names.ident(m.name.value)), ruleSide.twice,
    racing = LowerFaults.racing(v), assumed = v.models.flatMap(m => m.assumed.map(_.name -> m.name)).toMap)
  val env: LowerEnv = unclocked.copy(clock = v.models.flatMap(m => m.timed.map(LowerEnv.Clock(m.name, _,
    allows(m.name)))).headOption)

  /** Where the schedules let the world move the clock's time (owner §47): `fun w t => rule t w.other ∧ …`. */
  private def allows(clock: ModelName): LExpr =
    val (w, t) = (Names.builtin("w"), Names.builtin("s"))
    val rules = Outsides.schedules(resolved.theory, clock).map((_, f) => LExpr.Paren(LExpr.App(
      Atoms.define(unclocked, f.rule), LExpr.Name(t) :: f.over.map(o => LExpr.Dot(LExpr.Name(w), Names.ident(
        o.value).text)))))
    LExpr.Paren(LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(t)),
      rules.reduceOption(LExpr.Infix(LOp.And, _, _)).getOrElse(Atoms.name("True"))))
  /** A variable takes no name a symbol, a namespace (the FrModel's, a model's) or a name generated Lean writes itself
    * (`Reserved`) prints as, and no domain type's.
    */
  val naming: Naming = Naming.over(v.symbols.map(_.name.value).toSet ++ Reserved.names + kb.value ++
      v.models.map(_.name.value.capitalize),
    (v.types.map(_.typeName.value) ++ v.sorts.map(_.name.value) :+ "World").toSet).copy(canonical = canonical)
  /** What always holds that a statement takes: on a world, the rules of the stores it reads only (owner §33). */
  def guards(n: NodeId): List[Guard] = Guards.of(resolved.theory, n)
  /** The values provided where the code runs a statement mentions: what always holds of each is a hypothesis. */
  def provided(n: NodeId): List[(SymbolName, Ty)] = Reads.provided(resolved.theory, n)
  val props: LowerProp = LowerProp(table, env, naming, LowerProp.Values(fromOutside,
    s => resolved.theory.code.attached.get(s).exists(a => a.code.proven.nonEmpty || (a.code match
      case Code.Valued(_) | Code.Provided => true
      case Code.Modelled(_)               => !v.isAssumed(s)
      case _                              => false))))

  def node(n: NodeId): Boolean = resolved.theory.node(n).nonEmpty
  def isDefine(name: String): Boolean = v.defines.exists(d => d.name.value == name ||
    ruleSide.twice(d.name) && LowerEnv.guarded(d.name).value == name)
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
