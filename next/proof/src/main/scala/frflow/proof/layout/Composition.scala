package frflow.proof.layout

import frflow.core.analysis.SaysWhat
import frflow.core.name.{NodeId, SymbolName}
import frflow.proof.lean.ast.*
import frflow.proof.obligation.{Hyp, Prop, Required, Substitute}

/** How a node's claim is proven from what is below it, as terms over the theorems the node modules declare: `holds`
  * of a node with parts and no proven code (its `complete` applied to its parts' proofs), `impl` of one with proven
  * code (applied to what its code rests on), and a leaf's hypothesis `h_<Node>`. Every theorem is applied by name
  * (`(granted := granted) (h_A := …)`), each open term as it stands under `σ`.
  */
final class Composition(l: Lowering):
  private type Subst = Map[SymbolName, Substitute]
  private val t = l.resolved.theory
  private def parts(n: NodeId): List[NodeId] = t.refinement.parts(n)

  /** Checked against proven code (`impl`); a claim saying what a Declaration is is not: its code only stands in it. */
  def coded(n: NodeId): Boolean = SaysWhat.checkedAgainst(t, n).nonEmpty
  /** A node with a `holds`: parts, and no proven code (whose `impl` stands in its place). */
  def composed(n: NodeId): Boolean = !coded(n) && parts(n).nonEmpty

  /** What `holds` of a node assumes: the nodes below it with proven code or no parts. */
  def leaves(n: NodeId): List[NodeId] = if !composed(n) then List(n) else parts(n).flatMap(leaves).distinct

  /** `∀ U, h_L₁ → … → claim`: its claim from its leaves, over the open terms of every node composed in it. */
  def holds(n: NodeId): Prop = Prop.over(within(n), Prop.Implies(Hyp.parts(leaves(n)), Prop.claim(n)))

  private def within(n: NodeId): List[NodeId] = (n :: parts(n).filter(composed).flatMap(within)).distinct

  /** `fun U h_L₁ … => complete (x := x) … (h_P := …)`: `holds` from `complete` (`K.N.Auto.complete`, or the proof
    * file's) and each part's proof.
    */
  def holdsProof(n: NodeId, complete: LExpr, statement: Prop): LExpr =
    val names = Params.of(l.props.statement(holds(n)), Nil)
    Params.lambda(names, applied(complete, statement, Map.empty,
      parts(n).map(p => s"h_${p.value}" -> below(p))))

  /** A part's proof inside `holds`: its hypothesis, or its own `holds` applied to its leaves'. */
  private def below(p: NodeId): LExpr =
    if !composed(p) then LExpr.Name(Names.builtin(s"h_${p.value}"))
    else applied(theorem(p, "Theorems", "holds"), holds(p), Map.empty,
      leaves(p).map(x => s"h_${x.value}" -> LExpr.Name(Names.builtin(s"h_${x.value}"))))

  /** What the root's proof of the code rests on: the leaves below it that no proven code stands for. */
  def trusted(n: NodeId): List[NodeId] =
    if coded(n) then Required.hypotheses(l.resolved, n).flatMap(trusted).distinct
    else if composed(n) then leaves(n).flatMap(trusted).distinct
    else List(n)

  /** The statements of every theorem `proven(n, σ)` applies. */
  def involved(n: NodeId): List[Prop] =
    if coded(n) then implGoal(n).toList ++ Required.hypotheses(l.resolved, n).flatMap(involved)
    else if composed(n) then holds(n) :: leaves(n).flatMap(involved)
    else Nil

  /** A proof of `n`'s claim under `σ`, from the hypotheses `h_<T>` of what it trusts. */
  def proven(n: NodeId, σ: Subst): LExpr =
    if coded(n) then implGoal(n).fold(hypothesis(n))(goal => applied(theorem(n, "Impl", "impl"), goal, σ,
      Required.hypotheses(l.resolved, n).map(h => s"h_${h.value}" -> proven(h, σ))))
    else if composed(n) then applied(theorem(n, "Theorems", "holds"), holds(n), σ,
      leaves(n).map(x => s"h_${x.value}" -> proven(x, σ)))
    else hypothesis(n)

  private def implGoal(n: NodeId): Option[Prop] = Required.impl(l.resolved, n).headOption.map(_.goal)
  private def hypothesis(n: NodeId): LExpr = LExpr.Name(Names.builtin(s"h_${n.value}"))
  private def theorem(n: NodeId, module: String, name: String): LExpr =
    LExpr.Const(Names.path(l.kb.value, n.value, module, name))

  /** `(f (x := x) … (h_A := proof) …)`: `f`, whose statement is `statement`, applied by name. */
  def applied(f: LExpr, statement: Prop, σ: Subst, hyps: List[(String, LExpr)]): LExpr =
    val opens = l.props.opens(statement)
    val sorts = opens.sorts.map(s => Names.ident(s.value) -> LExpr.Name(Names.ident(s.value)))
    val symbols = opens.symbols.map(s => Names.ident(s.value) -> l.props.standing(s, σ))
    val outside = opens.symbols.flatMap(l.props.outsideNames).map(n => n -> LExpr.Name(n))
    val args = sorts ++ symbols ++ outside ++ hyps.map((h, e) => Names.builtin(h) -> e)
    LExpr.Paren(args.foldLeft(f)((g, a) => LExpr.Named(g, a._1, a._2)))
