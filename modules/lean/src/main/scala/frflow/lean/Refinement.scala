package frflow
package lean

/** How the nodes of a knowledge base refine each other in Lean: which nodes Lean states, their splits
  * and claims, the code proven of them, and what `holds` and `root_impl` are composed of.
  */
final class Refinement(kb: KnowledgeBase, val vocabulary: Vocabulary):
  import vocabulary.*
  private val K = kb.name

  /** Nodes with a statement Lean checks: formal claims, contracts and assumptions. */
  def formal(n: Node[?]): Boolean = kb.isStatement(n) && n.formal

  /** The parts that together refine a node, when Lean can state it: the node and every part formal. */
  def splitParts(n: Node[?]): Option[List[Node[?]]] =
    val ps = kb.parts(n)
    Option.when(formal(n) && ps.nonEmpty && ps.forall(formal))(ps)
  /** A node no formal split proves: a leaf of the composition (a hypothesis of what rests on it). */
  def leafy(n: Node[?]): Boolean = splitParts(n).isEmpty

  /** The invariants a contract keeps in Lean, each with the contract's view of a call. */
  def formalKeeps(n: Node[?]): List[(Node[?], Lifted[?])] =
    if !n.formal || n.kind != NodeKind.Contract then Nil
    else n.kept.collect { case Keep(i, Some(v), _) if i.formal && v.body.nonEmpty && i.rule.exists(_.body.nonEmpty) => (i, v) }

  /** The keepers of an invariant, each with its view (in Lean). */
  def keepers(i: Node[?]): List[(Node[?], Lifted[?])] =
    kb.nodes.flatMap(c => formalKeeps(c).filter(_._1 eq i).map(k => (c, k._2)))

  /** The implementation of a contract (or an assumption on an operation), when it is a `define` Lean can prove things about. */
  def provenImpl(n: Node[?]): Option[Def[?]] =
    if !formal(n) || n.op.isEmpty then None else kb.implementation(n).flatMap(_.proven)

  /** A declaration of a node's namespace. */
  def qualified(n: Node[?], decl: String): String = s"$K.${n.id}.$decl"

  /** The operation a node is about, as a term standing for itself. */
  private def opLeaf(n: Node[?]): Ctx = n.op.fold(Ctx.empty)(o => leaf(o.name))

  /** What the claim of a node takes. */
  def claimCtx(n: Node[?]): Ctx = (n.rule, n.post) match
    case (Some(r), _) => ctx(r) ++ Ctx.all(keepers(n).map((c, v) => ctx(v) ++ opLeaf(c)))
    case (_, Some(p)) => ctx(p) ++ opLeaf(n)
    case _            => n.formula.fold(Ctx.empty)(ctx(_))

  /** The claim of a node, applied to the terms (as `env` gives them), with the open terms it mentions. */
  def claim(n: Node[?], env: Env = Map.empty): (String, Ctx) = app(qualified(n, "claim"), claimCtx(n), env)

  /** The claims of some nodes, as named hypotheses `(h_X, claim of X)`, each with its open terms. */
  def hyps(ns: List[Node[?]], env: Env = Map.empty): List[((String, String), Ctx)] =
    ns.map(c => { val (t, o) = claim(c, env); ((s"h_${c.id}", t), o) })

  /** The open terms of a node's split: its own and its parts'. */
  def splitOpens(n: Node[?], parts: List[Node[?]]): Ctx = claim(n)._2 ++ Ctx.all(hyps(parts).map(_._2))

  /** The proven code of a node, as Lean, with the open terms it mentions (its callees' operations among them). */
  def code(d: Def[?], env: Env = Map.empty): (String, Ctx) = app(s"$K.${d.name}", defCtx(d), env)

  private def onOps(n: Node[?], ops: List[String]): List[Node[?]] =
    ops.filterNot(n.op.map(_.name).contains).flatMap(p => kb.onOp.getOrElse(p, Nil)).filter(formal).distinct

  /** The contracts (and assumptions) whose operations a node's code reads, itself or through the definitions
    * in force of the terms it reads: what its code depends on (and is composed after, in `root_impl`).
    */
  def callees(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => code(d)._2.params))

  /** The contracts (and assumptions) whose operations a node's code calls itself (or through the `define`s
    * it calls): what its code is proven from, the hypotheses of `impl`. An operation a term it reads is
    * defined with is not one: the definition is in the statement, not a promise the proof uses.
    */
  def calls(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => defCtx(d).params))

  /** The claim of a node with its operation replaced by its proven code: its statement, and the open
    * terms of `impl` (the claim's, and those of the promises of what the code calls).
    */
  def ofCode(n: Node[?], d: Def[?], op: String): (String, Ctx) =
    val (concl, co) = claim(n, Map(op -> code(d)))
    (concl, co ++ Ctx.all(hyps(calls(n)).map(_._2)))

  /** The leaves below a node (itself, if it is one): what `holds` takes as hypotheses. */
  def leaves(n: Node[?]): List[Node[?]] = splitParts(n).fold(List(n))(_.flatMap(leaves).distinctBy(_.id))

  /** The nodes the composition of `n` goes through: itself and every part below it, each once. */
  private def within(n: Node[?]): List[Node[?]] = (n :: splitParts(n).fold(Nil)(_.flatMap(within))).distinctBy(_.id)

  /** The open terms of `holds`: of every node it goes through (an intermediate node may mention a term
    * neither the node nor its leaves do).
    */
  def holdsOpens(n: Node[?], env: Env = Map.empty): Ctx = Ctx.all(within(n).map(claim(_, env)._2))

  def holdsStatement(n: Node[?]): String = stated(holdsOpens(n), hyps(leaves(n)).map(_._1), claim(n)._1)

  /** A proof of a node's claim inside `holds` of an ancestor: its hypothesis if it is a leaf, its own `holds` otherwise. */
  def proofOf(n: Node[?]): String =
    if leafy(n) then s"h_${n.id}"
    else s"(${qualified(n, "holds")} ${named(holdsOpens(n))} ${leaves(n).map(l => s"(h_${l.id} := h_${l.id})").mkString(" ")})"

  /** The contracts with proven code, each with that code and its operation. */
  private lazy val implemented: List[(Node[?], Def[?], String)] =
    kb.nodes.flatMap(c => for { d <- provenImpl(c) if c.kind == NodeKind.Contract; op <- c.op } yield (c, d, op.name))

  /** The operations with proven code, each with that code as Lean (its callees' code substituted). */
  lazy val codeEnv: Env =
    def go(env: Env, impl: (Node[?], Def[?], String), seen: Set[String]): Env =
      val (c, d, op) = impl
      if env.contains(op) || seen(op) then env
      else
        val below = callees(c).flatMap(x => implemented.find(_._1 eq x)).foldLeft(env)(go(_, _, seen + op))
        below.updated(op, code(d, below))
    implemented.foldLeft(Map.empty: Env)(go(_, _, Set.empty))

  /** The proven code `root_impl` puts in place of a node's operation, with the operation. */
  def implementing(n: Node[?]): Option[(Def[?], String)] =
    implemented.collectFirst { case (c, d, op) if (c eq n) && codeEnv.contains(op) => (d, op) }

  /** What `root_impl` assumes: the assumptions and the leaves no proven code implements, and the
    * contracts the proven code calls that no proven code implements.
    */
  lazy val trusted: List[Node[?]] =
    kb.root.filter(formal).toList.flatMap { r =>
      def need(n: Node[?], seen: Set[String], via: Node[?] => List[Node[?]]): List[Node[?]] =
        if seen(n.id) then Nil
        else if implementing(n).isDefined then via(n).flatMap(need(_, seen + n.id, via))
        else List(n)
      // What the proofs of the code call; listed in the order of what the code depends on.
      val used = leaves(r).flatMap(need(_, Set.empty, calls)).map(_.id).toSet
      leaves(r).flatMap(need(_, Set.empty, callees)).filter(n => used(n.id)).distinctBy(_.id)
    }

  /** Whether each node is shown to be met, by id (see `witnessed`), the parts of each before it. */
  private def witness(known: Map[String, Boolean], n: Node[?]): Map[String, Boolean] =
    if known.contains(n.id) then known
    else
      val parts = splitParts(n).getOrElse(Nil)
      val below = parts.foldLeft(known)(witness)
      below.updated(n.id, provenImpl(n).isDefined || n.kind == NodeKind.Assumption ||
        (parts.nonEmpty && parts.forall(p => below.getOrElse(p.id, false))))
  private lazy val witnesses: Map[String, Boolean] = kb.nodes.foldLeft(Map.empty[String, Boolean])(witness)

  /** Whether something is shown to meet the node: proven code, an assumption (whose consistency is
    * trusted), or parts that are all witnessed. A part nothing proves witnesses nothing, so a split
    * with one is asked for `feasible` even when another part has proven code below it.
    */
  def witnessed(n: Node[?]): Boolean = witness(witnesses, n).getOrElse(n.id, false)
