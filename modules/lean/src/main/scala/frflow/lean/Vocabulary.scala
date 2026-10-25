package frflow
package lean

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
      kb.nodes.flatMap(n => n.op.zip(n.post).map((o, p) =>
        // A flow's operation: from its input and a world, its result and the world after.
        o.name -> (if n.isFlow then n.opType.getOrElse(o.termType).lean.stripPrefix("(").stripSuffix(")") else p.params.map(_._2).mkString(" → "))))
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
