package frflow
package lean

/** The terms of a knowledge base in Lean. An open term (opaque type, parameter) is a binder; a defined
  * term is a `def` (a type: an `abbrev`) of the vocabulary. Every declaration takes the terms it mentions
  * as binders; every statement applies it to their definitions, so it is over the open terms only.
  *
  * @param chosen the definitions decided among alternatives (two definitions of one term)
  */
final class Vocabulary(kb: KnowledgeBase, chosen: String => Boolean):
  private val K = kb.name

  /** The definition in force of each defined term. */
  val inForce: Map[String, Node[?]] = kb.inForce(chosen)
  /** Terms with several definitions, none chosen yet: the nodes that use them wait for the choice. */
  val undecided: Set[String] = kb.definitionsOf.collect { case (t, ds) if ds.size > 1 && !inForce.contains(t) => t }.toSet

  def definitionOf(t: String): Option[Subst] = inForce.get(t).flatMap(_.substs.find(_.name == t))
  /** What a defined term that is not a type stands for. */
  def definedTerm(t: String): Option[Lifted[?]] = definitionOf(t).filterNot(_.isType).flatMap(_.term)

  /** Each term a definition in force fixes, with the definition and what it says of the term, by name. */
  lazy val definitionsInForce: List[(String, Node[?], Subst)] =
    inForce.toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t).map(s => (t, d, s)))

  val defNames: Set[String] = kb.defs.map(_.name).toSet
  private val defByName: Map[String, Def[?]] = kb.defs.map(d => d.name -> d).toMap
  private val opaqueNames: Set[String] = kb.opaques.map(_.name).toSet
  def isOpaque(name: String): Boolean = opaqueNames(name)

  private val paramTypes: Map[String, String] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(_.paramRefs).toMap ++
      kb.nodes.flatMap(n => n.op.zip(n.post).map((o, p) => o.name -> p.params.map(_._2).mkString(" → ")))
  /** The Lean type of a parameter. */
  def paramType(p: String): Option[String] = paramTypes.get(p)

  /** What a lifted expression mentions, and what the `define`s it calls need (those in `self` excluded:
    * a recursive one), given the contexts of the `define`s known so far.
    */
  private def ctxOf(l: Lifted[?], self: Set[String], known: Map[String, Ctx]): Ctx =
    Ctx(l.opaques, l.paramRefs.map(_._1)) ++
      Ctx.all(l.defs.filterNot(d => self(d.name)).map(d => known.getOrElse(d.name, ctxOf(d.lifted, self + d.name, known))))

  /** The context of every `define`, built in the order `kb.defs` lists them: dependencies first. */
  private lazy val defCtxs: Map[String, Ctx] =
    kb.defs.foldLeft(Map.empty[String, Ctx])((known, d) => known.updated(d.name, ctxOf(d.lifted, Set(d.name), known)))

  /** The terms a `define` takes. */
  def defCtx(d: Def[?]): Ctx = defCtxs.getOrElse(d.name, ctxOf(d.lifted, Set(d.name), defCtxs))

  /** Context of a lifted expression: what it mentions, and what the functions it calls need. */
  def ctx(l: Lifted[?]): Ctx = ctxOf(l, Set.empty, defCtxs)

  /** A term standing for itself: an opaque type, or a parameter with the open types its type names. */
  def leaf(x: String): Ctx =
    if opaqueNames(x) then Ctx(List(x), Nil)
    else Ctx("""[A-Za-z_][\w']*""".r.findAllIn(paramTypes.getOrElse(x, "")).filter(o => opaqueNames(o) && !inForce.contains(o)).toList.distinct, List(x))

  /** Lean for what a term stands for, with the open terms it mentions: itself when open, its definition
    * when defined (applied to its terms, recursively), or what `env` gives it.
    */
  def term(x: String, env: Env = Map.empty): (String, Ctx) =
    env.getOrElse(x, definitionOf(x) match
      case Some(s) if s.isType => (s.lean, Ctx.empty)
      case Some(s)             => s.term.fold((x, leaf(x)))(l => app(s"$K.$x", ctx(l), env))
      case None                => (x, leaf(x)))

  /** `f` applied to the terms of `c`, each as `term` gives it. */
  def app(f: String, c: Ctx, env: Env = Map.empty): (String, Ctx) =
    val ts = c.names.map(term(_, env))
    (if ts.isEmpty then f else s"($f ${ts.map(_._1).mkString(" ")})", Ctx.all(ts.map(_._2)))

  def binders(c: Ctx): String =
    val ts = if c.opaques.isEmpty then Nil else List(s"(${c.opaques.mkString(" ")} : Type)")
    val ps = c.params.map(p => s"($p : ${paramTypes.getOrElse(p, "_")})")
    (ts ++ ps).mkString(" ")

  /** `∀ terms, ∀ (h_X : X) ..., conclusion`. */
  def stated(opens: Ctx, hyps: List[(String, String)], conclusion: String): String = LeanText.forall(binders(opens), hyps, conclusion)

  /** `f` applied to the binders in scope named as the terms of `c` (inside a declaration). */
  def ref(f: String, c: Ctx): String = if c.isEmpty then f else s"($f ${c.names.mkString(" ")})"

  /** `f := term` for each term of `c`: named arguments. */
  def named(c: Ctx, env: Env = Map.empty): String = c.names.map(x => s"($x := ${term(x, env)._1})").mkString(" ")

  /** Replaces `⟦f⟧` by `f` applied to the terms it takes (as written: the binders in scope). */
  def resolve(lean: String): String =
    """⟦([^⟧]+)⟧""".r.replaceAllIn(lean, m =>
      scala.util.matching.Regex.quoteReplacement(defByName.get(m.group(1)).fold(s"$K.${m.group(1)}")(d =>
        if defCtx(d).isEmpty then s"$K.${d.name}" else s"($K.${d.name} ${defCtx(d).names.mkString(" ")})")))

  /** The terms a node uses that wait for a choice between two definitions. */
  def waitsForDefinition(n: Node[?]): List[String] =
    def go(ts: List[String], seen: Set[String]): List[String] = ts.flatMap { t =>
      if seen(t) then Nil else if undecided(t) then List(t) else definitionOf(t).flatMap(_.term).fold(Nil)(l => go(ctx(l).names, seen + t))
    }
    go(kb.termsOf(n), Set.empty).distinct
