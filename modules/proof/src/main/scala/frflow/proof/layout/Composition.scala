package frflow.proof.layout

import cats.Eval
import frflow.core.analysis.resolution.SaysWhat
import frflow.core.graph.Walk
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.proof.lean.ast.*
import frflow.proof.obligation.{Hyp, Made, Obligation, ObligationName, Prop, Required, Substitute}

/** How a node's claim is proven from what is below it, as terms over the theorems the node modules declare: `holds`
  * of a node with parts and no proven code (its `complete` applied to its parts' proofs), `impl` of one with proven
  * code (applied to what its code rests on), and a leaf's hypothesis `h_<Node>`. Every theorem is applied by name
  * (`(granted := granted) (h_A := …)`), each open term as it stands under `σ`. What a node rests on is a DAG, so
  * each node's is read once (`Eval`), and a proof used more than once below a root is named once (`proven`).
  */
final class Composition(l: Lowering):
  private type Subst = Map[SymbolName, Substitute]
  private val t = l.resolved.theory
  private def parts(n: NodeId): List[NodeId] = t.refinement.parts(n)
  private val ids = t.nodes.map(_.node.id)
  private def once[K, V](keys: List[K])(f: K => V): K => V =
    val memo = keys.map(k => k -> Eval.later(f(k))).toMap
    k => memo.get(k).fold(f(k))(_.value)
  private lazy val hypotheses: NodeId => List[NodeId] = once(ids)(Required.hypotheses(l.resolved, _))
  private lazy val reliedOnBy: SymbolName => List[NodeId] =
    once(t.vocabulary.symbols.map(_.name))(l.resolved.reliedOnBy)

  /** Checked against proven code (`impl`); a claim saying what a Declaration is is not: its code only stands in it. */
  def coded(n: NodeId): Boolean = SaysWhat.checkedAgainst(t, n).nonEmpty
  /** A node with a `holds`: parts, and no proven code (whose `impl` stands in its place). */
  def composed(n: NodeId): Boolean = !coded(n) && parts(n).nonEmpty

  /** What `holds` of a node assumes: the nodes below it with proven code or no parts. */
  def leaves(n: NodeId): List[NodeId] = if !composed(n) then List(n) else parts(n).flatMap(leaves).distinct

  /** `∀ U, h_L₁ → … → m_… → claim`: its claim from its leaves and what the makers below it make (`Made.taken`),
    * over the open terms of every node composed in it.
    */
  def holds(n: NodeId): Prop =
    Prop.over(within(n), Prop.Implies(Hyp.parts(leaves(n)) ++ made(n).map(_._3), Prop.claim(n)))

  /** What the steps composed in `n` take of the makers below them, each once. */
  private def made(n: NodeId): List[(NodeId, SymbolName, Hyp)] =
    within(n).flatMap(Made.taken(l.resolved, _)).distinctBy(_._3.name)

  private def within(n: NodeId): List[NodeId] = (n :: parts(n).filter(composed).flatMap(within)).distinct

  /** `fun U h_L₁ … => complete (x := x) … (h_P := …)`: `holds` from `complete` (`K.N.Auto.complete`, or the proof
    * file's) and each part's proof.
    */
  def holdsProof(n: NodeId, complete: LExpr, statement: Prop): LExpr =
    val names = Params.of(l.props.statement(holds(n)), Nil)
    Params.lambda(names, applied(complete, statement, Map.empty,
      parts(n).map(p => LeanNames.hypothesis(p) -> below(p)) ++
        Made.taken(l.resolved, n).map(m => m._3.name -> name(m._3))))

  /** A part's proof inside `holds`: its hypothesis, or its own `holds` applied to its leaves'. */
  private def below(p: NodeId): LExpr =
    if !composed(p) then LExpr.Name(Names.builtin(LeanNames.hypothesis(p)))
    else applied(theorem(p, "Theorems", "holds"), holds(p), Map.empty,
      leaves(p).map(x => LeanNames.hypothesis(x) -> LExpr.Name(Names.builtin(LeanNames.hypothesis(x)))) ++
        made(p).map(m => m._3.name -> name(m._3)))

  private def name(h: Hyp): LExpr = LExpr.Name(Names.builtin(h.name))

  /** What the root's proof of the code rests on: the leaves below it that no proven code stands for. */
  def trusted(n: NodeId): List[NodeId] = trustedOf(n)
  private lazy val trustedOf: NodeId => List[NodeId] = once(ids) { n =>
    if coded(n) then hypotheses(n).flatMap(trusted).distinct
    else if composed(n) then (leaves(n).flatMap(trusted) ++ made(n).flatMap(m => madeTrusted(m._1, m._2))).distinct
    else List(n)
  }

  private def madeTrusted(rule: NodeId, op: SymbolName): List[NodeId] =
    reliedOnBy(op).flatMap(trusted) ++ Made.callees(l.resolved, rule, op).flatMap(madeTrusted(rule, _))

  /** The statements of every theorem `proven(n, σ)` applies, each once. */
  def involved(n: NodeId): List[Prop] = involvedOf(n)
  private lazy val involvedOf: NodeId => List[Prop] = once(ids) { n =>
    if coded(n) then (implGoal(n).toList ++ hypotheses(n).flatMap(involved)).distinct
    else if composed(n) then
      (holds(n) :: leaves(n).flatMap(involved) ++ made(n).flatMap(m => madeInvolved(m._1, m._2))).distinct
    else Nil
  }

  private def madeInvolved(rule: NodeId, op: SymbolName): List[Prop] =
    madeGoal(rule, op).toList ++ reliedOnBy(op).flatMap(involved) ++
      Made.callees(l.resolved, rule, op).flatMap(madeInvolved(rule, _))

  private def madeGoal(rule: NodeId, op: SymbolName): Option[Prop] =
    madeOf(rule).find(_.name == ObligationName.Made(op.value)).map(_.goal)
  private lazy val madeOf: NodeId => List[Obligation] = once(ids)(Made.of(l.resolved, _))

  /** A proof of what `op` makes meeting the rule, under `σ`: its `made_` theorem applied to what its code relies on
    * and to what its callees make, each node's proof as `ref` gives it.
    */
  private def madeProof(rule: NodeId, op: SymbolName, σ: Subst, ref: NodeId => LExpr): LExpr =
    madeGoal(rule, op).fold(LExpr.Name(Names.builtin(LeanNames.madeTaken(rule, op))))(goal =>
      applied(theorem(rule, "Checks", LeanNames.Made + op.value), goal, σ,
        reliedOnBy(op).map(h => LeanNames.hypothesis(h) -> ref(h)) ++
          Made.callees(l.resolved, rule, op).map(c => LeanNames.madeByCallee(c) -> madeProof(rule, c, σ, ref))))

  /** A proof of `n`'s claim under `σ`, from the hypotheses `h_<T>` of what it trusts. Each proof below it that its
    * term would use more than once is named once before it, children first (`let p_<N> : claim := …`), so the term
    * grows with the nodes below `n`, not with the paths to them.
    */
  def proven(n: NodeId, σ: Subst): LExpr =
    val order = applying(n)
    val uses = order.flatMap(refs).groupMapReduce(identity)(_ => 1)(_ + _)
    val shared = order.filter(m => m != n && uses.getOrElse(m, 0) > 1 && (coded(m) && implGoal(m).nonEmpty ||
      composed(m))).toSet
    def ref(m: NodeId): LExpr = if shared(m) then LExpr.Name(Names.builtin(s"p_${m.value}")) else step(m, σ, ref)
    order.filter(shared).foldRight(step(n, σ, ref))((m, body) =>
      LExpr.Let(Names.builtin(s"p_${m.value}"), l.props.statement(Prop.ClaimOf(m, σ)), step(m, σ, ref), body))

  /** `n`'s proof, each proof it applies as `ref` gives it. */
  private def step(n: NodeId, σ: Subst, ref: NodeId => LExpr): LExpr =
    if coded(n) then implGoal(n).fold(hypothesis(n))(goal => applied(theorem(n, "Impl", "impl"), goal, σ,
      hypotheses(n).map(h => LeanNames.hypothesis(h) -> ref(h))))
    else if composed(n) then applied(theorem(n, "Theorems", "holds"), holds(n), σ,
      leaves(n).map(x => LeanNames.hypothesis(x) -> ref(x)) ++
        made(n).map(m => m._3.name -> madeProof(m._1, m._2, σ, ref)))
    else hypothesis(n)

  /** The nodes whose proofs `n`'s applies, once each time it does (through the `made_` proofs it applies too). */
  private def refs(n: NodeId): List[NodeId] =
    if coded(n) then implGoal(n).fold(Nil)(_ => hypotheses(n))
    else if composed(n) then leaves(n) ++ made(n).flatMap(m => madeRefs(m._1, m._2))
    else Nil

  private def madeRefs(rule: NodeId, op: SymbolName): List[NodeId] =
    madeGoal(rule, op).fold(Nil)(_ => reliedOnBy(op) ++ Made.callees(l.resolved, rule, op).flatMap(madeRefs(rule, _)))

  /** `n` and every node its proof applies, below it, each once, each after those its proof applies. */
  private def applying(n: NodeId): List[NodeId] = Walk.postorder(List(n), identity)(refs(_).distinct)

  private lazy val implGoal: NodeId => Option[Prop] =
    once(ids)(n => Required.impl(l.resolved, n).headOption.map(_.goal))
  private def hypothesis(n: NodeId): LExpr = LExpr.Name(Names.builtin(LeanNames.hypothesis(n)))
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
