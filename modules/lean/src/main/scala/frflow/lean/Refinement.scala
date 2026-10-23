package frflow
package lean

import frflow.protocol.NodeKind

/** The terms in Lean: an open one is a binder of each declaration mentioning it, a defined one a `def` statements apply. */
final class Vocabulary(kb: KnowledgeBase, chosen: String => Boolean):
  private val K = kb.name
  val inForce: Map[String, Node[?]] = kb.inForce(chosen)
  /** Terms with several definitions, none chosen yet: the nodes that use them wait for the choice. */
  val undecided: Set[String] = kb.definitionsOf.collect { case (t, ds) if ds.size > 1 && !inForce.contains(t) => t }.toSet
  def definitionOf(t: String): Option[Subst] = inForce.get(t).flatMap(_.substs.find(_.name == t))
  def definedTerm(t: String): Option[Lifted[?]] = definitionOf(t).filterNot(_.isType).flatMap(_.term)
  lazy val definitionsInForce: List[(String, Node[?], Subst)] =
    inForce.toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t).map(s => (t, d, s)))
  val defNames: Set[String] = kb.defs.map(_.name).toSet
  private val defByName: Map[String, Def[?]] = kb.defs.map(d => d.name -> d).toMap
  private val opaqueNames: Set[String] = kb.opaques.map(_.name).toSet
  def isOpaque(name: String): Boolean = opaqueNames(name)
  private val paramTypes: Map[String, String] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(_.paramRefs).toMap ++
      kb.nodes.flatMap(n => n.op.zip(n.post).map((o, p) => o.name -> p.params.map(_._2).mkString(" → ")))
  def paramType(p: String): Option[String] = paramTypes.get(p)

  // What a lifted expression mentions, and what the `define`s it calls need (`self` excluded: a recursive one).
  private def ctxOf(l: Lifted[?], self: Set[String], known: Map[String, Ctx]): Ctx =
    Ctx(l.opaques, l.paramRefs.map(_._1)) ++
      Ctx.all(l.defs.filterNot(d => self(d.name)).map(d => known.getOrElse(d.name, ctxOf(d.lifted, self + d.name, known))))
  private lazy val defCtxs: Map[String, Ctx] =
    kb.defs.foldLeft(Map.empty[String, Ctx])((known, d) => known.updated(d.name, ctxOf(d.lifted, Set(d.name), known)))
  def defCtx(d: Def[?]): Ctx = defCtxs.getOrElse(d.name, ctxOf(d.lifted, Set(d.name), defCtxs))
  def ctx(l: Lifted[?]): Ctx = ctxOf(l, Set.empty, defCtxs)

  def leaf(x: String): Ctx =
    if opaqueNames(x) then Ctx(List(x), Nil)
    else Ctx("""[A-Za-z_][\w']*""".r.findAllIn(paramTypes.getOrElse(x, "")).filter(o => opaqueNames(o) && !inForce.contains(o)).toList.distinct, List(x))

  /** Itself when open, its definition (applied to its terms) when defined, or what `env` gives it. */
  def term(x: String, env: Env = Map.empty): (String, Ctx) =
    env.getOrElse(x, definitionOf(x) match
      case Some(s) if s.isType => (s.lean, Ctx.empty)
      case Some(s)             => s.term.fold((x, leaf(x)))(l => app(s"$K.$x", ctx(l), env))
      case None                => (x, leaf(x)))

  def app(f: String, c: Ctx, env: Env = Map.empty): (String, Ctx) =
    val ts = c.names.map(term(_, env))
    (if ts.isEmpty then f else s"($f ${ts.map(_._1).mkString(" ")})", Ctx.all(ts.map(_._2)))

  def binders(c: Ctx): String =
    (Option.when(c.opaques.nonEmpty)(s"(${c.opaques.mkString(" ")} : Type)") ++ c.params.map(p => s"($p : ${paramTypes.getOrElse(p, "_")})")).mkString(" ")
  def stated(opens: Ctx, hyps: List[(String, String)], conclusion: String): String = LeanText.forall(binders(opens), hyps, conclusion)
  /** `f` applied to the binders in scope named as the terms of `c` (inside a declaration). */
  def ref(f: String, c: Ctx): String = if c.isEmpty then f else s"($f ${c.names.mkString(" ")})"
  def named(c: Ctx, env: Env = Map.empty): String = c.names.map(x => s"($x := ${term(x, env)._1})").mkString(" ")

  /** Replaces `⟦f⟧` by `f` applied to the terms it takes (as written: the binders in scope). */
  def resolve(lean: String): String =
    """⟦([^⟧]+)⟧""".r.replaceAllIn(lean, m =>
      scala.util.matching.Regex.quoteReplacement(defByName.get(m.group(1)).fold(s"$K.${m.group(1)}")(d =>
        if defCtx(d).isEmpty then s"$K.${d.name}" else s"($K.${d.name} ${defCtx(d).names.mkString(" ")})")))

  def waitsForDefinition(n: Node[?]): List[String] =
    def go(ts: List[String], seen: Set[String]): List[String] = ts.flatMap { t =>
      if seen(t) then Nil else if undecided(t) then List(t) else definitionOf(t).flatMap(_.term).fold(Nil)(l => go(ctx(l).names, seen + t))
    }
    go(kb.termsOf(n), Set.empty).distinct

/** How the nodes refine each other in Lean: their claims and splits, their proven code, `holds` and `root_impl`. */
final class Refinement(kb: KnowledgeBase, val vocabulary: Vocabulary):
  import vocabulary.*
  private val K = kb.name
  def formal(n: Node[?]): Boolean = kb.isStatement(n)
  def splitParts(n: Node[?]): Option[List[Node[?]]] = Option.when(formal(n))(kb.parts(n)).filter(_.nonEmpty)
  def leafy(n: Node[?]): Boolean = splitParts(n).isEmpty
  def formalKeeps(n: Node[?]): List[(Node[?], Lifted[?])] =
    if n.kind != NodeKind.Contract then Nil else n.kept.collect { case Keep(i, Some(v), _) if i.rule.isDefined => (i, v) }
  def keepers(i: Node[?]): List[(Node[?], Lifted[?])] =
    kb.nodes.flatMap(c => formalKeeps(c).filter(_._1 eq i).map(k => (c, k._2)))
  def provenImpl(n: Node[?]): Option[Def[?]] =
    if !formal(n) || n.op.isEmpty then None else kb.implementation(n).flatMap(_.proven)
  def qualified(n: Node[?], decl: String): String = s"$K.${n.id}.$decl"
  private def opLeaf(n: Node[?]): Ctx = n.op.fold(Ctx.empty)(o => leaf(o.name))

  def claimCtx(n: Node[?]): Ctx = (n.rule, n.post) match
    case (Some(r), _) => ctx(r) ++ Ctx.all(keepers(n).map((c, v) => ctx(v) ++ opLeaf(c)))
    case (_, Some(p)) => ctx(p) ++ opLeaf(n)
    case _            => n.formula.fold(Ctx.empty)(ctx(_))
  def claim(n: Node[?], env: Env = Map.empty): (String, Ctx) = app(qualified(n, "claim"), claimCtx(n), env)
  def hyps(ns: List[Node[?]], env: Env = Map.empty): List[((String, String), Ctx)] =
    ns.map(c => { val (t, o) = claim(c, env); ((s"h_${c.id}", t), o) })
  def splitOpens(n: Node[?], parts: List[Node[?]]): Ctx = claim(n)._2 ++ Ctx.all(hyps(parts).map(_._2))
  def code(d: Def[?], env: Env = Map.empty): (String, Ctx) = app(s"$K.${d.name}", defCtx(d), env)
  private def onOps(n: Node[?], ops: List[String]): List[Node[?]] =
    ops.filterNot(n.op.map(_.name).contains).flatMap(p => kb.onOp.getOrElse(p, Nil)).filter(formal).distinct
  /** Whose operations the node's code reads, also through defined terms: composed before it in `root_impl`. */
  def callees(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => code(d)._2.params))
  /** Whose operations the code calls: `impl`'s hypotheses (a term's definition is in the statement, not one of them). */
  def calls(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => defCtx(d).params))

  def ofCode(n: Node[?], d: Def[?], op: String): (String, Ctx) =
    val (concl, co) = claim(n, Map(op -> code(d)))
    (concl, co ++ Ctx.all(hyps(calls(n)).map(_._2)))
  /** What `holds` takes as hypotheses: the leaves below a node (itself, if it is one). */
  def leaves(n: Node[?]): List[Node[?]] = splitParts(n).fold(List(n))(_.flatMap(leaves).distinctBy(_.id))
  private def within(n: Node[?]): List[Node[?]] = (n :: splitParts(n).fold(Nil)(_.flatMap(within))).distinctBy(_.id)
  /** Of every node `holds` goes through: an intermediate node may mention a term neither the node nor its leaves do. */
  def holdsOpens(n: Node[?], env: Env = Map.empty): Ctx = Ctx.all(within(n).map(claim(_, env)._2))
  def holdsStatement(n: Node[?]): String = stated(holdsOpens(n), hyps(leaves(n)).map(_._1), claim(n)._1)

  def proofOf(n: Node[?]): String =
    if leafy(n) then s"h_${n.id}"
    else s"(${qualified(n, LeanText.Holds)} ${named(holdsOpens(n))} ${leaves(n).map(l => s"(h_${l.id} := h_${l.id})").mkString(" ")})"
  private lazy val implemented: List[(Node[?], Def[?], String)] =
    kb.nodes.flatMap(c => for { d <- provenImpl(c) if c.kind == NodeKind.Contract; op <- c.op } yield (c, d, op.name))

  lazy val codeEnv: Env =
    def go(env: Env, impl: (Node[?], Def[?], String), seen: Set[String]): Env =
      val (c, d, op) = impl
      if env.contains(op) || seen(op) then env
      else
        val below = callees(c).flatMap(x => implemented.find(_._1 eq x)).foldLeft(env)(go(_, _, seen + op))
        below.updated(op, code(d, below))
    implemented.foldLeft(Map.empty: Env)(go(_, _, Set.empty))
  def implementing(n: Node[?]): Option[(Def[?], String)] =
    implemented.collectFirst { case (c, d, op) if (c eq n) && codeEnv.contains(op) => (d, op) }

  /** What `root_impl` assumes: the assumptions, leaves and called contracts no proven code implements. */
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

  private def witness(known: Map[String, Boolean], n: Node[?]): Map[String, Boolean] =
    if known.contains(n.id) then known
    else
      val parts = splitParts(n).getOrElse(Nil)
      val below = parts.foldLeft(known)(witness)
      below.updated(n.id, provenImpl(n).isDefined || n.kind == NodeKind.Assumption ||
        (parts.nonEmpty && parts.forall(p => below.getOrElse(p.id, false))))
  private lazy val witnesses: Map[String, Boolean] = kb.nodes.foldLeft(Map.empty[String, Boolean])(witness)

  /** Shown to be met: by proven code, an assumption, or parts that all are (a part nothing proves witnesses nothing). */
  def witnessed(n: Node[?]): Boolean = witness(witnesses, n).getOrElse(n.id, false)
