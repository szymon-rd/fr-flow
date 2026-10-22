package frflow

import scala.collection.mutable

/** A statement Lean is asked to prove (or, for a try, that it is asked whether it can prove). */
final case class Obligation(name: String, statement: String, description: String)

/** Generates the Lean of a knowledge base (docs/DAG.md §3). Layout, relative to the Lean workspace:
  *
  *   - `FrFlowGen/<KB>/Domain.lean`          the vocabulary: domain types, `define`s, and the definitions in force
  *   - `FrFlowGen/<KB>/<Node>/Spec.lean`     the node's claim and the statements of its obligations
  *   - `FrFlowGen/<KB>/<Node>/Auto.lean`     `complete` by `frflow_auto`, unless proven by hand
  *   - `FrFlowGen/<KB>/<Node>/Theorems.lean` `holds`: the node, from the leaves below it
  *   - `FrFlowGen/<KB>/<Node>/Impl.lean`     `impl`: its proven code meets the contract
  *   - `FrFlowGen/<KB>/<Node>/Eval.lean`     the examples, evaluated
  *   - `FrFlowGen/<KB>/<Node>/Checks.lean`   the tries (needed, clash, unsat, idle) and the other obligations
  *   - `FrFlowGen/<KB>/RootImpl.lean`        `root_impl`: the root, of the code, from the trusted leaves
  *
  * An open term (opaque type, parameter) is a Lean binder; a defined term is a `def` (a type: an
  * `abbrev`) of the vocabulary. Every declaration takes the terms it mentions as binders; every statement
  * applies it to their definitions, so it is over the open terms only.
  *
  * @param authored (node, obligation) proven by a theorem of that name in `Proofs/<KB>/<Node>.lean`
  * @param chosen   the definitions decided among alternatives (two definitions of one term)
  */
object Generate:
  /** Names the generated Lean binds itself; a parameter or opaque type with one of them would be captured. */
  val reserved: Set[String] =
    Set("m", "f", "h", "p", "claim", "post", "rule", "holds", "complete", "impl", "Obl", "Type", "Prop",
      "some", "none", "True", "False", "true", "false", "max", "min", "decide", "List", "Option", "Int", "Nat", "Bool", "String",
      "Prod", "Exists", "Eq", "Ne", "Not", "And", "Or", "Iff", "id", "ite", "Classical", "Unit", "FrFlow") ++ (0 to 9).map(i => s"x$i")

  /** How many probes of a contract Lean evaluates, beside its examples. */
  val Probes = 6

  /** The work a try (a statement Lean is asked whether it can prove) may take: a try is one-sided and cheap. */
  val TryHeartbeats = 40000

  /** The numbers a value holds, however nested: the boundaries a probe tries. */
  def numbers(v: Any): List[BigInt] = v match
    case i: Int     => List(BigInt(i))
    case l: Long    => List(BigInt(l))
    case b: BigInt  => List(b)
    case l: Iterable[?] => l.toList.flatMap(numbers)
    case Some(x)    => numbers(x)
    case p: Product => p.productIterator.toList.flatMap(numbers)
    case _          => Nil

  /** Values of the same type near `v`: a number at the boundaries (`nums`, and next to it), a list
    * emptied, shortened, reversed, with its head again or with a row like its head added, a string emptied, an option empty, a case
    * class or tuple with one field changed so. What the examples do not reach, the translation is
    * checked on.
    */
  def near(v: Any, nums: List[BigInt]): List[Any] =
    val out: List[Any] = v match
      case b: Boolean => List(!b)
      case i: Int     => (nums.filter(_.isValidInt).map(_.toInt) ++ List(0, i + 1, i - 1, -i))
      case l: Long    => (nums.filter(_.isValidLong).map(_.toLong) ++ List(0L, l + 1, l - 1, -l))
      case b: BigInt  => nums ++ List(BigInt(0), b + 1, b - 1, -b)
      case s: String  => List("", s + s)
      case Some(x)    => None :: near(x, nums).take(2).map(Some(_))
      case l: List[?] => if l.isEmpty then Nil else List(Nil, l.tail, l.reverse, l.head :: l) ++ near(l.head, nums).take(2).map(x => l :+ x)
      case p: Product if p.productArity > 0 =>
        val fields = p.productIterator.toList
        val make = p.getClass.getConstructors.find(_.getParameterCount == fields.size)
        make.toList.flatMap(k => fields.indices.flatMap(i => near(fields(i), nums).take(3).flatMap(x =>
          scala.util.Try(k.newInstance(fields.updated(i, x).map(_.asInstanceOf[AnyRef])*)).toOption)))
      case _ => Nil
    out.distinct.filter(_ != v)

  /** The top-level arrows of a Lean type: `A → (B → C) → D` is `A`, `(B → C)`, `D`. */
  def arrows(t0: String): List[String] =
    def depth(t: String) = t.scanLeft(0)((d, c) => if c == '(' then d + 1 else if c == ')' then d - 1 else d)
    val t = { val x = t0.trim; if x.startsWith("(") && x.endsWith(")") && depth(x.init.tail).forall(_ >= 0) then x.init.tail.trim else x }
    val out = mutable.ListBuffer.empty[String]; var d = 0; var from = 0
    t.indices.foreach { i =>
      if t(i) == '(' then d += 1 else if t(i) == ')' then d -= 1
      else if d == 0 && t.startsWith(" → ", i) then { out += t.substring(from, i); from = i + 3 }
    }
    (out += t.substring(from)).toList.map(_.trim)

final class Generate(kb: KnowledgeBase, authored: Set[(String, String)] = Set.empty, chosen: String => Boolean = _ => false):
  import Generate.*
  /** Whether the proof file of `n` proves its obligation `name`. */
  def isAuthored(n: Node[?], name: String): Boolean = authored((n.id, name))
  private val K = kb.name

  def specModule(id: String) = s"FrFlowGen.$K.$id.Spec"
  def autoModule(id: String) = s"FrFlowGen.$K.$id.Auto"
  def theoremsModule(id: String) = s"FrFlowGen.$K.$id.Theorems"
  def implModule(id: String) = s"FrFlowGen.$K.$id.Impl"
  def proofsModule(id: String) = s"Proofs.$K.$id"
  def rootImplModule = s"FrFlowGen.$K.RootImpl"
  def specPath(id: String) = s"FrFlowGen/$K/$id/Spec.lean"
  def autoPath(id: String) = s"FrFlowGen/$K/$id/Auto.lean"
  def theoremsPath(id: String) = s"FrFlowGen/$K/$id/Theorems.lean"
  def implPath(id: String) = s"FrFlowGen/$K/$id/Impl.lean"
  def proofsPath(id: String) = s"Proofs/$K/$id.lean"
  def checksPath(id: String) = s"FrFlowGen/$K/$id/Checks.lean"
  def evalPath(id: String) = s"FrFlowGen/$K/$id/Eval.lean"
  def rootImplPath = s"FrFlowGen/$K/RootImpl.lean"
  /** Lemmas the proof files of this knowledge base share. */
  def lemmasModule = s"Proofs.$K.Lemmas"
  def lemmasPath = s"Proofs/$K/Lemmas.lean"
  def generatedDirs = List(s"FrFlowGen/$K", s"FrFlowAudit/$K")

  private val Header = "-- GENERATED by FrFlow from the Scala model. Do not edit.\n\n"
  /** The equations of every `match` a module declares, generated in it: two modules generating them
    * each would declare Lean's auxiliary `_sparseCasesOn` twice, and a module importing both fails.
    */
  private val MatchEqns = "frflow_match_eqns\n"
  private val Preamble = "set_option autoImplicit false\nset_option linter.unusedVariables false\nnoncomputable section\nopen Classical\n\n"

  // ---------------------------------------------------------------------------
  // The vocabulary: open and defined terms
  // ---------------------------------------------------------------------------

  /** The definition in force of each defined term. */
  val inForce: Map[String, Node[?]] = kb.inForce(chosen)
  /** Terms with several definitions, none chosen yet: the nodes that use them wait for the choice. */
  val undecided: Set[String] = kb.definitionsOf.collect { case (t, ds) if ds.size > 1 && !inForce.contains(t) => t }.toSet
  private def definitionOf(t: String): Option[Subst] = inForce.get(t).flatMap(_.substs.find(_.name == t))

  /** The opaque types and parameters a declaration takes, by name, in order (types first). */
  final case class Ctx(opaques: List[String], params: List[String]):
    def ++(o: Ctx): Ctx = Ctx((opaques ++ o.opaques).distinct, (params ++ o.params).distinct)
    def names: List[String] = opaques ++ params
    def isEmpty: Boolean = names.isEmpty

  object Ctx:
    val empty: Ctx = Ctx(Nil, Nil)
    def all(cs: Iterable[Ctx]): Ctx = cs.foldLeft(empty)(_ ++ _)

  private val opaqueNames: Set[String] = kb.opaques.map(_.name).toSet
  private val paramTypes: Map[String, String] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(_.paramRefs).toMap ++
      kb.nodes.flatMap(n => n.op.zip(n.post).map((o, p) => o.name -> p.params.map(_._2).mkString(" → ")))
  private val defByName: Map[String, Def[?]] = kb.defs.map(d => d.name -> d).toMap
  private val defCtxCache = mutable.Map.empty[String, Ctx]

  private def defCtx(d: Def[?]): Ctx = defCtxCache.synchronized {
    defCtxCache.getOrElseUpdate(d.name, {
      defCtxCache(d.name) = Ctx.empty // recursion
      ctx(d.lifted, Set(d.name))
    })
  }

  /** Context of a lifted expression: what it mentions, and what the functions it calls need. */
  def ctx(l: Lifted[?], self: Set[String] = Set.empty): Ctx =
    val own = Ctx(l.opaques, l.paramRefs.map(_._1))
    own ++ Ctx.all(l.defs.filterNot(d => self(d.name)).map(defCtx))

  /** A term standing for itself: an opaque type, or a parameter with the open types its type names. */
  private def leaf(x: String): Ctx =
    if opaqueNames(x) then Ctx(List(x), Nil)
    else Ctx("""[A-Za-z_][\w']*""".r.findAllIn(paramTypes.getOrElse(x, "")).filter(o => opaqueNames(o) && !inForce.contains(o)).toList.distinct, List(x))

  /** Lean for what a term stands for, with the open terms it mentions: itself when open, its definition
    * when defined (applied to its terms, recursively), or what `env` gives it (code, doing nothing, a value).
    */
  type Env = Map[String, (String, Ctx)]
  def term(x: String, env: Env = Map.empty): (String, Ctx) =
    env.getOrElse(x, definitionOf(x) match
      case Some(s) if s.isType => (s.lean, Ctx.empty)
      case Some(s)             => app(s"$K.$x", ctx(s.term.get), env)
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
  private def stated(opens: Ctx, hyps: List[(String, String)], conclusion: String): String =
    val b = binders(opens)
    (if b.isEmpty then "" else s"∀ $b, ") + (if hyps.isEmpty then "" else s"∀ ${hyps.map((h, t) => s"($h : $t)").mkString(" ")}, ") + conclusion

  /** `f` applied to the binders in scope named as the terms of `c` (inside a declaration). */
  private def ref(f: String, c: Ctx): String = if c.isEmpty then f else s"($f ${c.names.mkString(" ")})"

  /** Replaces `⟦f⟧` by `f` applied to the terms it takes (as written: the binders in scope). */
  def resolve(lean: String): String =
    """⟦([^⟧]+)⟧""".r.replaceAllIn(lean, m =>
      scala.util.matching.Regex.quoteReplacement(defByName.get(m.group(1)).fold(s"$K.${m.group(1)}")(d =>
        if defCtx(d).isEmpty then s"$K.${d.name}" else s"($K.${d.name} ${defCtx(d).names.mkString(" ")})")))

  // ---------------------------------------------------------------------------
  // Nodes
  // ---------------------------------------------------------------------------

  /** Nodes with a statement Lean checks: formal claims, contracts and assumptions. */
  def formal(n: Node[?]): Boolean = kb.isStatement(n) && n.formal

  /** The terms a node uses that wait for a choice between two definitions. */
  def waitsForDefinition(n: Node[?]): List[String] =
    def go(ts: List[String], seen: Set[String]): List[String] = ts.flatMap { t =>
      if seen(t) then Nil else if undecided(t) then List(t) else definitionOf(t).flatMap(_.term).fold(Nil)(l => go(ctx(l).names, seen + t))
    }
    go(kb.termsOf(n), Set.empty).distinct

  /** The parts that together refine a node, when Lean can state it: the node and every part formal. */
  def splitParts(n: Node[?]): Option[List[Node[?]]] =
    val ps = kb.parts(n)
    Option.when(formal(n) && ps.nonEmpty && ps.forall(formal))(ps)
  /** A node no formal split proves: a leaf of the composition (a hypothesis of what rests on it). */
  def leafy(n: Node[?]): Boolean = splitParts(n).isEmpty

  /** The invariants a contract keeps in Lean, each with the contract's view of a call. */
  def formalKeeps(n: Node[?]): List[(Node[?], Lifted[?])] =
    if !n.formal || n.kind != NodeKind.Contract then Nil
    else n.kept.collect { case Keep(i, Some(v), _, _) if i.formal && v.body.nonEmpty && i.rule.exists(_.body.nonEmpty) => (i, v) }

  /** The keepers of an invariant, each with its view (in Lean). */
  private def keepers(i: Node[?]): List[(Node[?], Lifted[?])] =
    kb.nodes.flatMap(c => formalKeeps(c).filter(_._1 eq i).map(k => (c, k._2)))

  /** The implementation of a contract (or an assumption on an operation), when it is a `define` Lean can prove things about. */
  def provenImpl(n: Node[?]): Option[Def[?]] =
    if !formal(n) || n.op.isEmpty then None else kb.implementation(n).flatMap(_.proven)

  private def q(n: Node[?], decl: String) = s"$K.${n.id}.$decl"
  private def opOf(n: Node[?]): String = n.op.get.name

  /** What the claim of a node takes. */
  def claimCtx(n: Node[?]): Ctx =
    if n.isInvariant then ctx(n.rule.get) ++ Ctx.all(keepers(n).map((c, v) => ctx(v) ++ leaf(opOf(c))))
    else if n.post.isDefined then ctx(n.post.get) ++ leaf(opOf(n))
    else n.formula.fold(Ctx.empty)(ctx(_))

  /** The claim of a node, applied to the terms (as `env` gives them), with the open terms it mentions. */
  def claim(n: Node[?], env: Env = Map.empty): (String, Ctx) = app(q(n, "claim"), claimCtx(n), env)

  /** The Lean of a call `op x0 x1`, under the post's input names. */
  private def call(ts: List[String]) = (ts.zipWithIndex.map((t, i) => s"(x$i : $t)").mkString(" "), ts.indices.map(i => s"x$i").mkString(" "))

  // ---------------------------------------------------------------------------
  // Files
  // ---------------------------------------------------------------------------

  def files: Map[String, String] =
    val perNode = kb.nodes.filter(formal).flatMap { n =>
      List(specPath(n.id) -> spec(n), autoPath(n.id) -> auto(n), theoremsPath(n.id) -> theorems(n), checksPath(n.id) -> checks(n)) ++
        provenImpl(n).map(_ => implPath(n.id) -> impl(n)) ++ evalFile(n).map(evalPath(n.id) -> _)
    }
    (s"FrFlowGen/$K/Domain.lean" -> domain :: rootImpl.map((_, text) => rootImplPath -> text).toList ++ perNode).toMap

  /** Lean of the domain types, functions and definitions a node's own expressions use. */
  def declarationsUsedBy(n: Node[?]): List[String] =
    val defs = Def.closure((n.lifted ++ formalKeeps(n).flatMap(_._1.rule)).flatMap(_.defs) ++ provenImpl(n))
    val ls = n.lifted ++ formalKeeps(n).flatMap(_._1.rule) ++ defs.map(_.lifted)
    ls.flatMap(_.types).map(_.lean).distinct ++ defs.map(d => resolve(d.lifted.lean)) ++
      kb.definitionsUsed(n, inForce).flatMap(_.substs).map(s => s"${s.name} := ${s.lean}")

  /** What a node uses, as written in Scala: the domain types and the `define`s, however nested. Part of
    * what a decision is bound to; unlike the generated Lean, it does not change when FrFlow's translation does.
    */
  def sourcesUsedBy(n: Node[?]): List[String] =
    val defs = Def.closure(n.referenced.flatMap(_.defs))
    val types = (n.referenced ++ defs.map(_.lifted)).flatMap(_.types) ++ n.substs.flatMap(_.types)
    types.map(t => if t.scala.nonEmpty then t.scala else t.lean).distinct ++ defs.map(d => s"${d.name} = ${d.lifted.source}")

  /** The vocabulary module: the domain types, the `define`s (over the terms they mention), the types
    * defined (`abbrev`) and the terms defined (`def`, over the terms their definitions mention).
    */
  def domain: String =
    val defs = kb.defs.map { d =>
      val b = binders(defCtx(d))
      s"@[frflow_defs] def ${d.name}${if b.isEmpty then "" else " " + b} : ${d.lifted.leanType} :=\n  ${resolve(d.lifted.lean)}"
    }
    val definitions = inForce.toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t).map(s => (t, d, s)))
    val types = definitions.collect { case (t, d, s) if s.isType => s"/-- ${d.id} -/\n@[frflow_defs] abbrev $t : Type := ${s.lean}" }
    val terms = definitions.collect { case (t, d, s) if !s.isType =>
      val l = s.term.get
      val b = binders(ctx(l))
      s"/-- ${d.id} -/\n@[frflow_defs] def $t${if b.isEmpty then "" else " " + b} : ${l.leanType} :=\n  ${resolve(l.lean)}"
    }
    Header + "import FrFlow\n\n" + Preamble + s"namespace $K\n\n" + (kb.types.map(_.lean) ++ types ++ defs ++ terms).mkString("\n\n") + s"\n\n$MatchEqns\nend $K\n"

  // ---------------------------------------------------------------------------
  // Obligations
  // ---------------------------------------------------------------------------

  /** A proposition each named hypothesis of which is a claim: `(h_X, claim of X)`. */
  private def hyps(ns: List[Node[?]], env: Env = Map.empty): List[((String, String), Ctx)] =
    ns.map(c => { val (t, o) = claim(c, env); ((s"h_${c.id}", t), o) })

  /** The open terms of a node's split: its own and its parts'. */
  private def splitOpens(n: Node[?], parts: List[Node[?]]): Ctx = claim(n)._2 ++ Ctx.all(hyps(parts).map(_._2))

  /** The contracts (and assumptions) whose operations a node's code calls: what its code is proven from. */
  def callees(n: Node[?]): List[Node[?]] =
    provenImpl(n).toList.flatMap(d => app(s"$K.${d.name}", defCtx(d))._2.params).filterNot(n.op.map(_.name).contains)
      .flatMap(p => kb.onOp.getOrElse(p, Nil)).filter(formal).distinct

  /** The code of a node, as Lean, with the open terms it mentions (its callees' operations among them). */
  private def code(n: Node[?], env: Env = Map.empty): (String, Ctx) =
    val d = provenImpl(n).get
    app(s"$K.${d.name}", defCtx(d), env)

  /** Doing nothing, for an operation of type `t`: returning `[]`, `none`, `False`, or an input unchanged. */
  private def nothing(t: String): Option[String] =
    val ps = arrows(t)
    val r = ps.last
    val ins = ps.init
    val v = if ins.isEmpty then None
      else if r == "Prop" then Some("False")
      else if r.startsWith("(List ") || r.startsWith("List ") then Some("[]")
      else if r.startsWith("(Option ") || r.startsWith("Option ") then Some("none")
      else ins.indexOf(r) match { case -1 => None; case i => Some(s"x$i") }
    v.map(b => s"(fun ${ins.indices.map(i => s"(x$i : ${ins(i)})").mkString(" ")} => $b)")

  /** The obligations of a node: its split, its code, its cheap check, its kept invariants' coverage,
    * the expectations; `feasible` with an authored split. Each is proven by `frflow_auto` or authored.
    */
  def obligations(n: Node[?]): List[Obligation] =
    val complete = splitParts(n).map { ps =>
      val hs = hyps(ps)
      Obligation("complete", stated(splitOpens(n, ps), hs.map(_._1), claim(n)._1), s"The parts of ${n.id} (${ps.map(_.id).mkString(", ")}) together make it.")
    }
    // A proof the agent wrote may rest on a contradiction automation did not find: then something
    // must meet the parts. A proven implementation below the node is that witness.
    val feasible = splitParts(n).filter(_ => isAuthored(n, "complete") && !witnessed(n)).map { ps =>
      val o = splitOpens(n, ps)
      val b = binders(o)
      Obligation("feasible", s"${if b.isEmpty then "" else s"∃ $b, "}${hyps(ps).map(_._1._2).mkString(" ∧ ")}",
        s"Some world meets the parts of ${n.id}: its authored proof does not rest on a contradiction.")
    }
    val implementation = provenImpl(n).map { d =>
      val (c, o) = code(n)
      val (concl, co) = claim(n, Map(opOf(n) -> (c, o)))
      val hs = hyps(callees(n))
      Obligation("impl", stated(co ++ Ctx.all(hs.map(_._2)), hs.map(_._1), concl),
        s"Every result of ${d.name} meets ${n.id}${if hs.isEmpty then "" else s", given what ${callees(n).map(_.id).mkString(", ")} promise"}.")
    }
    val check = n.local.filter(_ => n.post.isDefined && formal(n)).map { l =>
      val (vars, xs) = call(n.post.get.params.map(_._2))
      val (p, po) = app(q(n, "post"), ctx(n.post.get))
      val (c, cc) = app(q(n, "runCheck"), ctx(l))
      Obligation("check", stated(po ++ cc, Nil, s"∀ $vars, $p $xs → $c $xs"),
        s"What service checks of ${n.id} on every call follows from its post: it refuses nothing the contract allows.")
    }
    val covers = formalKeeps(n).flatMap { (inv, _) =>
      coverage(n, inv).toOption.flatten.map((stmt, o) => Obligation(s"cover_${inv.id}", stated(o, Nil, stmt),
        s"The view of ${inv.id} lists all the result holds of it, each with the caller."))
    }
    val expects = Option.when(formal(n))(n.expected).toList.flatten.zipWithIndex.map { case ((statement, l), i) =>
      val (c, co) = claim(n)
      val (e, eo) = app(q(n, s"expected_$i"), ctx(l))
      Obligation(s"expect_$i", stated(co ++ eo, List("h" -> c), e), statement)
    }
    complete.toList ++ feasible ++ implementation ++ check ++ covers ++ expects

  def obligation(n: Node[?], name: String): Option[Obligation] = obligations(n).find(_.name == name)

  /** A try: a statement Lean is asked whether it can prove, cheaply; if it does, `means` what is wrong. */
  final case class Try(obligation: Obligation, means: String)

  /** The tries of a node: a part not needed (with one part: the node says nothing it adds), parts that
    * contradict each other, no world meeting the node, an expectation that checks nothing, and, for the
    * root, doing nothing meeting it.
    */
  def tries(n: Node[?]): List[Try] =
    val split = splitParts(n).toList.flatMap { ps =>
      val o = splitOpens(n, ps)
      val hs = hyps(ps)
      val needed = if ps.size == 1 then List(Try(Obligation("vacuous", stated(o, Nil, claim(n)._1), s"${n.id} holds whatever ${ps.head.id} says."),
          s"${n.id} holds whatever ${ps.head.id} says: it says nothing its part adds"))
        else ps.map(c => Try(Obligation(s"needed_${c.id}", stated(o, hs.filterNot(_._1._1 == s"h_${c.id}").map(_._1), claim(n)._1),
          s"${n.id} holds without ${c.id}."), s"${c.id} is not needed for ${n.id}"))
      needed :+ Try(Obligation("clash", stated(o, hs.map(_._1), "False"), s"The parts of ${n.id} contradict each other."),
        s"the parts of ${n.id} contradict each other: no world meets them all")
    }
    val (c, co) = claim(n)
    val unsat = Try(Obligation("unsat", stated(co, Nil, s"¬ $c"), s"No world meets ${n.id}."), s"${n.id} is contradictory: no world meets it")
    val expects = n.expected.indices.toList.map { i =>
      val (e, eo) = app(q(n, s"expected_$i"), ctx(n.expected(i)._2))
      Try(Obligation(s"vacuous_expect_$i", stated(eo, Nil, e), s"The expectation holds whatever ${n.id} says."),
        "the expectation holds whatever the node says: it checks nothing")
    }
    if !formal(n) then Nil else split ++ List(unsat) ++ expects ++ idle(n).map(o => Try(o, s"doing nothing meets ${n.id}"))

  /** The root with every operation it mentions replaced by doing nothing (see `nothing`), when one can be. */
  def idle(n: Node[?]): Option[Obligation] =
    if !kb.root.exists(_ eq n) || !formal(n) then None
    else
      val ops = claim(n)._2.params.filter(kb.isOp)
      val env: Env = ops.flatMap(o => nothing(paramTypes.getOrElse(o, "")).map(v => o -> (v, leaf(o).copy(params = Nil)))).toMap
      Option.when(env.nonEmpty) {
        val (c, o) = claim(n, env)
        Obligation("idle", stated(o, Nil, c), s"${n.id} is met by doing nothing (${env.keys.toList.sorted.mkString(", ")}: returning nothing).")
      }

  /** What doing nothing is, in words, for the root's idle. */
  def idleWhat(n: Node[?]): String =
    claim(n)._2.params.filter(kb.isOp).filter(o => nothing(paramTypes.getOrElse(o, "")).isDefined).mkString(", ") + " doing nothing"

  // ---------------------------------------------------------------------------
  // Composition: holds, and the root of the code
  // ---------------------------------------------------------------------------

  /** The leaves below a node (itself, if it is one): what `holds` takes as hypotheses. */
  def leaves(n: Node[?]): List[Node[?]] =
    if leafy(n) then List(n) else splitParts(n).get.flatMap(leaves).distinctBy(_.id)

  /** The nodes the composition of `n` goes through: itself and every part below it, each once. */
  private def within(n: Node[?]): List[Node[?]] =
    (n :: (if leafy(n) then Nil else splitParts(n).get.flatMap(within))).distinctBy(_.id)

  /** The open terms of `holds`: of every node it goes through (an intermediate node may mention a term
    * neither the node nor its leaves do).
    */
  private def holdsOpens(n: Node[?], env: Env = Map.empty): Ctx = Ctx.all(within(n).map(claim(_, env)._2))

  def holdsStatement(n: Node[?]): String = stated(holdsOpens(n), hyps(leaves(n)).map(_._1), claim(n)._1)

  private def named(c: Ctx, env: Env = Map.empty): String = c.names.map(x => s"($x := ${term(x, env)._1})").mkString(" ")

  /** A proof of a node's claim inside `holds` of an ancestor: its hypothesis if it is a leaf, its own `holds` otherwise. */
  private def proofOf(n: Node[?]): String =
    if leafy(n) then s"h_${n.id}"
    else s"(${q(n, "holds")} ${named(holdsOpens(n))} ${leaves(n).map(l => s"(h_${l.id} := h_${l.id})").mkString(" ")})"

  /** The operations with proven code, each with that code as Lean (its callees' code substituted). */
  lazy val codeEnv: Env =
    val impls = kb.nodes.filter(c => c.kind == NodeKind.Contract && provenImpl(c).isDefined)
    val env = mutable.Map.empty[String, (String, Ctx)]
    def go(c: Node[?], seen: Set[String]): Unit =
      val o = opOf(c)
      if !env.contains(o) && !seen(o) then
        callees(c).filter(x => impls.exists(_ eq x)).foreach(go(_, seen + o))
        env(o) = code(c, env.toMap)
    impls.foreach(go(_, Set.empty))
    env.toMap

  /** The node whose proven code implements an operation in `root_impl`. */
  private def implementing(n: Node[?]): Boolean = n.kind == NodeKind.Contract && provenImpl(n).isDefined && codeEnv.contains(opOf(n))

  /** What `root_impl` assumes: the assumptions and the leaves no proven code implements, and the
    * contracts the proven code calls that no proven code implements.
    */
  lazy val trusted: List[Node[?]] =
    kb.root.filter(formal).toList.flatMap { r =>
      def need(n: Node[?], seen: Set[String]): List[Node[?]] =
        if seen(n.id) then Nil
        else if implementing(n) then callees(n).flatMap(need(_, seen + n.id))
        else List(n)
      leaves(r).flatMap(need(_, Set.empty)).distinctBy(_.id)
    }

  /** `root_impl`: the root of the code (every implemented operation replaced by its code), from the
    * trusted leaves alone; with its proof, composed from `holds` and the `impl` theorems.
    */
  def rootImpl: Option[(String, String)] =
    kb.root.filter(formal).map { r =>
      def implProof(n: Node[?]): String =
        val (c, o) = code(n)
        val (_, co) = claim(n, Map(opOf(n) -> (c, o)))
        val opens = co ++ Ctx.all(hyps(callees(n)).map(_._2))
        s"(${q(n, "Impl.impl")} ${named(opens, codeEnv)} ${callees(n).map(c => s"(h_${c.id} := ${proofIn(c)})").mkString(" ")})"
      def proofIn(n: Node[?]): String = if implementing(n) then implProof(n) else s"h_${n.id}"
      val hs = hyps(trusted, codeEnv)
      val (concl, co) = claim(r, codeEnv)
      // Every term the composition mentions once the code is in: the code's own inputs among them.
      val implOpens = kb.nodes.filter(implementing).map { n =>
        val (c, o) = code(n)
        val (_, cco) = claim(n, Map(opOf(n) -> (c, o)))
        Ctx.all((cco ++ Ctx.all(hyps(callees(n)).map(_._2))).names.map(term(_, codeEnv)._2))
      }
      val opens = co ++ Ctx.all(hs.map(_._2)) ++ holdsOpens(r, codeEnv) ++ Ctx.all(implOpens)
      val statement = stated(opens, hs.map(_._1), concl)
      val intro = opens.names ++ trusted.map(t => s"h_${t.id}")
      val proof = s"by\n${if intro.isEmpty then "" else s"  intro ${intro.mkString(" ")}\n"}  exact ${q(r, "holds")} ${named(holdsOpens(r), codeEnv)} " +
        leaves(r).map(l => s"(h_${l.id} := ${proofIn(l)})").mkString(" ")
      val imports = (List(theoremsModule(r.id)) ++ kb.nodes.filter(implementing).map(n => implModule(n.id))).distinct
      (statement, Header + imports.map(m => s"import $m\n").mkString + "\n" + Preamble + s"namespace $K.RootImpl\n\n" +
        s"/-- The root holds of the code, from what is trusted: ${if trusted.isEmpty then "nothing" else trusted.map(_.id).mkString(", ")}. -/\n" +
        s"theorem root_impl : $statement :=\n  $proof\n\n#print axioms $K.RootImpl.root_impl\n\nend $K.RootImpl\n")
    }

  /** The nodes on the path of a proven implementation: something is shown to meet them. */
  private lazy val witnessedIds: Set[String] =
    kb.nodes.filter(provenImpl(_).isDefined).flatMap(c => c :: kb.ancestors(c)).map(_.id).toSet
  def witnessed(n: Node[?]): Boolean = witnessedIds(n.id)

  // ---------------------------------------------------------------------------
  // What a result holds: for the coverage of an invariant's view
  // ---------------------------------------------------------------------------

  /** A Lean type, read back from its text. */
  private enum LT:
    case Name(n: String)
    case ListOf(t: LT)
    case OptionOf(t: LT)
    case Prod(a: LT, b: LT)
    case Fun(text: String)

  private def parseType(t0: String): LT =
    val t = t0.trim
    def depthZero(sym: String): Option[Int] =
      var d = 0
      (0 until t.length).find { i =>
        val c = t(i)
        if c == '(' then d += 1 else if c == ')' then d -= 1
        d == 0 && t.startsWith(sym, i)
      }
    def closes(i: Int): Int =
      var d = 0
      (i until t.length).find { j => if t(j) == '(' then d += 1 else if t(j) == ')' then d -= 1; d == 0 }.getOrElse(-1)
    if t.startsWith("(") && closes(0) == t.length - 1 then parseType(t.substring(1, t.length - 1))
    else if depthZero("→").isDefined then LT.Fun(t)
    else depthZero("×") match
      case Some(i) => LT.Prod(parseType(t.take(i)), parseType(t.drop(i + 1)))
      case None if t.startsWith("List ") => LT.ListOf(parseType(t.drop(5)))
      case None if t.startsWith("Option ") => LT.OptionOf(parseType(t.drop(7)))
      case None => LT.Name(t)

  private val typeDecls: Map[String, TypeDecl] = kb.types.map(t => t.name -> t).toMap

  /** `y` occurs in `x` of type `t`, as a Lean proposition: None if a value of `t` can never hold one of
    * `target`; Left for a type FrFlow cannot unfold (a recursive one).
    */
  private def occurs(y: String, x: String, t: LT, target: LT, seen: Set[String] = Set.empty): Either[String, Option[String]] =
    val fresh = s"z${seen.size}_${x.count(_ == '.')}${x.length}'"
    def any(parts: List[Either[String, Option[String]]]): Either[String, Option[String]] =
      parts.collectFirst { case Left(w) => w }.toLeft {
        val ps = parts.collect { case Right(Some(p)) => p }
        Option.when(ps.nonEmpty)(ps.mkString("(", " ∨ ", ")"))
      }
    if t == target then Right(Some(s"$y = $x"))
    else t match
      case LT.ListOf(e)   => occurs(y, fresh, e, target, seen).map(_.map(b => s"(∃ $fresh ∈ $x, $b)"))
      case LT.OptionOf(e) => occurs(y, fresh, e, target, seen).map(_.map(b => s"(∃ $fresh, $x = some $fresh ∧ $b)"))
      case LT.Prod(a, b)  => any(List(occurs(y, s"$x.1", a, target, seen), occurs(y, s"$x.2", b, target, seen)))
      // A function can hold what it returns (or takes): what the view must list of it cannot be stated.
      case LT.Fun(text)   =>
        val names = """[A-Za-z_][\w.]*""".r.findAllIn(text).toSet
        val t = target match { case LT.Name(n) => Some(n); case _ => None }
        if t.exists(n => names(n) || names.exists(m => typeDecls.get(m).exists(_.uses.contains(n)))) then
          Left(s"the result is a function ($text), which can hold a ${t.getOrElse("")}: what the view must list of it cannot be stated")
        else Right(None)
      case LT.Name(n) => typeDecls.get(n) match
        case None => Right(None)
        case Some(_) if seen(n) => Left(s"$n is recursive")
        case Some(d) if d.ctors.size == 1 && d.ctors.head._1 == "mk" =>
          any(d.ctors.head._2.map((f, ft) => occurs(y, s"$x.$f", parseType(ft), target, seen + n)))
        case Some(d) =>
          val cases = d.ctors.map { (c, fs) =>
            val vars = fs.indices.map(i => s"${fresh}$i").toList
            (c, vars, any(fs.zip(vars).map { case ((_, ft), v) => occurs(y, v, parseType(ft), target, seen + n) }))
          }
          cases.collectFirst { case (_, _, Left(w)) => w }.toLeft {
            Option.when(cases.exists(_._3.exists(_.isDefined)))(cases.map { (c, vs, b) =>
              s"| $n.$c${vs.map(" " + _).mkString} => ${b.toOption.flatten.getOrElse("False")}"
            }.mkString(s"(match $x with ", " ", ")"))
          }

  /** That a contract's view of an invariant lists every value of the rule's type the result holds,
    * each paired with the call's input of the rule's first type (when exactly one input has it): a view
    * cannot leave out, or pair with someone else, what the result shows. Left when it cannot be stated;
    * else the statement (over the result as `x<last>`) and the terms it mentions.
    */
  def coverage(n: Node[?], inv: Node[?]): Either[String, Option[(String, Ctx)]] =
    val ts = n.post.get.params.map(_._2)
    val rule = inv.rule.get.params.map(_._2)
    val target = parseType(rule(1))
    // About a value of the domain (a record, an opaque thing), not a number or a string, which every
    // result may hold for other reasons.
    val domain = target match
      case LT.Name(t) => typeDecls.contains(t) || opaqueNames(t)
      case _          => false
    val view = formalKeeps(n).find(_._1 eq inv).get._2
    val (v, vo) = app(q(n, s"view_${inv.id}"), ctx(view))
    if !domain then Right(None) else occurs("y'", s"x${ts.size - 1}", parseType(ts.last), target).map(_.map { occ =>
      val pair = readerOf(n, inv).fold("p.2 = y'")(i => s"p.1 = x$i ∧ p.2 = y'")
      val (vars, xs) = call(ts)
      (s"∀ $vars, ∀ (y' : ${rule(1)}), $occ → ∃ p ∈ $v $xs, $pair", vo)
    }).flatMap(c => if c.isDefined && readerOf(n, inv).isEmpty && readers(n, inv).size > 1 then
        Left(s"${readers(n, inv).size} inputs are of the rule's first type: say which the pairs are about (.keeps(${inv.id}, reader = i), counting from 0)")
      else Right(c))

  /** The inputs of a contract of the rule's first type (who a call shows things to). */
  private def readers(n: Node[?], inv: Node[?]): List[Int] =
    val rule = inv.rule.get.params.map(_._2)
    n.post.get.params.map(_._2).init.zipWithIndex.filter((t, _) => parseType(t) == parseType(rule(0))).map(_._2)

  /** The input the view's pairs are about: named in `keeps`, or the only one of the rule's first type. */
  private def readerOf(n: Node[?], inv: Node[?]): Option[Int] =
    n.kept.find(_.invariant eq inv).map(_.reader).filter(_ >= 0).orElse(readers(n, inv) match { case List(i) => Some(i); case _ => None })

  // ---------------------------------------------------------------------------
  // Examples, evaluated in Lean
  // ---------------------------------------------------------------------------

  private val typeNames: Set[String] = kb.types.map(_.name).toSet
  /** Lean parameter names, with the Param objects they stand for. */
  private val paramObject: Map[String, Param[?]] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(l => l.paramRefs.map(_._1).zip(l.paramObjects)).toMap ++
      kb.nodes.flatMap(_.op).map(o => o.name -> o)

  /** The Lean name of a domain class, as `Lift` declares it (the owner chain without packages). */
  private def leanName(c: Class[?]): String =
    val pkg = c.getPackageName
    val rest = if pkg.isEmpty then c.getName else c.getName.stripPrefix(pkg + ".")
    rest.replaceAll("[^$]*\\$package\\$", "").split('$').filter(_.nonEmpty).map(Names.ident).mkString(".")

  /** A Scala value as a Lean term of the domain: None for what Lean has no value for (a function, an
    * opaque value, a Map).
    */
  def leanValue(v: Any): Option[String] =
    def all(xs: Iterator[Any]) = { val ts = xs.map(leanValue).toList; Option.when(ts.forall(_.isDefined))(ts.flatten) }
    def int(b: BigInt) = if b < 0 then s"($b)" else b.toString
    def ctor(name: String, args: List[String]) = if args.isEmpty then s"$K.$name" else s"($K.$name ${args.mkString(" ")})"
    v match
      case b: Boolean => Some(if b then "True" else "False")
      case i: Int     => Some(int(BigInt(i)))
      case l: Long    => Some(int(BigInt(l)))
      case b: BigInt  => Some(int(b))
      case s: String  => Some(Names.string(s))
      case ()         => Some("()")
      case None       => Some("none")
      case Some(x)    => leanValue(x).map(t => s"(some $t)")
      case l: List[?] => all(l.iterator).map(_.mkString("[", ", ", "]"))
      // A map, as the function Lean has for it (see `Lift.tpe`); a set, as its membership.
      case m: Map[?, ?] => all(m.iterator.flatMap((k, v) => List(k, v))).map(_.grouped(2).toList
        .foldRight("none")((kv, rest) => s"if k' = ${kv(0)} then some ${kv(1)} else $rest")).map(b => s"(fun k' => $b)")
      case st: Set[?] => all(st.iterator).map(xs => s"(fun y' => ${(xs.map(x => s"y' = $x") :+ "False").mkString(" ∨ ")})")
      case t: Product if t.getClass.getName.startsWith("scala.Tuple") => all(t.productIterator).map(_.mkString("(", ", ", ")"))
      case e: scala.reflect.Enum =>
        val c = if typeNames(leanName(e.getClass)) then e.getClass else e.getClass.getSuperclass
        Option.when(typeNames(leanName(c)))(leanName(c)).flatMap(t => all(e.productIterator).map(ctor(s"$t.${Names.ident(e.productPrefix)}", _)))
      case p: Product if typeNames(leanName(p.getClass)) => all(p.productIterator).map(ctor(s"${leanName(p.getClass)}.mk", _))
      case _ => None

  /** An example, evaluated in Lean: `claim` is what Scala computes of it (the contract's verdict, or the
    * result of the proven implementation), `opposite` its negation. Lean proving the opposite means the
    * translation does not mean what the Scala does.
    */
  final case class Eval(name: String, what: String, claim: String, opposite: String)

  /** The examples of a contract Lean evaluates, and why the others are not evaluated (by `eval_i`); then
    * probes (`probe_j`): inputs near the examples' (see `near`), each run in Scala and evaluated in Lean, so
    * that the translation is cross-checked where the examples do not reach. A probe Lean cannot evaluate
    * is left out; one it evaluates otherwise than Scala fails the node, as an example does.
    */
  def evals(n: Node[?]): (List[Eval], List[(String, String)]) =
    if !formal(n) || n.post.isEmpty then (Nil, Nil)
    else
      val post = n.post.get.value.asInstanceOf[(Any, Any, Any) => Boolean]
      val impl = provenImpl(n)
      def one(name: String, label: String, bindings: List[Binding], a: Any, b: Any, result: Option[Any]): Either[String, List[Eval]] =
        // Each open term, by the value the example gives it; an operation by its proven code.
        def valueOf(p: String, seen: Set[String]): Either[String, String] =
          paramObject.get(p).flatMap(po => bindings.find(_.param eq po)) match
            case Some(b) if b.table.isDefined =>
              // A finite table: a function that looks it up.
              val dom = paramTypes.get(p).map(parseType) match
                case Some(LT.Fun(t)) => t.stripPrefix("(").stripSuffix(")").split("→").headOption.map(_.trim)
                case _               => None
              val cases = b.table.get.toList.map((k, v) => for { tk <- leanValue(k); tv <- leanValue(v) } yield (tk, tv))
              if dom.isEmpty || cases.exists(_.isEmpty) then Left(s"Lean has no value for the table $p")
              else Right(s"(fun (k' : ${dom.get}) => ${cases.flatten.foldRight("none")((kv, rest) => s"if k' = ${kv._1} then some ${kv._2} else $rest")})")
            case Some(b) =>
              scala.util.Try(b.value()).toOption.flatMap(leanValue).toRight(s"Lean has no value for $p (a function, or a type Lean does not have; give a lookup as bindTable)")
            // A call of another operation: in Lean, its proven code (which the example runs).
            case None if kb.onOp.getOrElse(p, Nil).exists(c => provenImpl(c).isDefined) && !seen(p) =>
              val c = kb.onOp(p).find(c => provenImpl(c).isDefined).get
              envOf(defCtx(provenImpl(c).get), seen + p).map(env => app(s"$K.${provenImpl(c).get.name}", defCtx(provenImpl(c).get), env)._1)
            case None => Left(s"it gives no value for $p")
        def envOf(c: Ctx, seen: Set[String]): Either[String, Env] =
          val opens = Ctx.all(c.names.map(term(_)._2))
          if opens.opaques.nonEmpty then Left(s"the contract leaves ${opens.opaques.mkString(", ")} open")
          else opens.params.foldRight(Right(Map.empty): Either[String, Env])((p, acc) => for { v <- valueOf(p, seen); r <- acc } yield r + (p -> (v, Ctx.empty)))
        for
          env <- envOf(ctx(n.post.get) ++ provenImpl(n).fold(Ctx.empty)(defCtx), Set(n.op.get.name))
          // A probe has no result of its own: the implementation's, when there is one.
          ran <- scala.util.Try(Bindings.within(kb.opCode ++ kb.definitionBindings ++ bindings) {
              val got = impl.map(d => d.fn.asInstanceOf[(Any, Any) => Any](a, b))
              val r = result.orElse(got)
              (r.map(post(a, b, _)), got)
            }).toEither.left.map(x => s"Scala cannot evaluate it: ${x.getMessage}")
          ta <- leanValue(a).toRight("Lean has no value for its input")
          tb <- leanValue(b).toRight("Lean has no value for its input")
          tr <- ran._1.fold(Right(None): Either[String, Option[String]])(_ => leanValue(result.orElse(ran._2).get).map(Some(_)).toRight("Lean has no value for its result"))
        yield
          val (verdict, got) = ran
          val onPost = for { v <- verdict; t <- tr } yield
            val call = s"${app(q(n, "post"), ctx(n.post.get), env)._1} $ta $tb $t"
            Eval(name, label, if v then call else s"¬ $call", if v then s"¬ $call" else call)
          val onImpl = for { d <- impl; g <- got; tg <- leanValue(g) } yield
            val f = app(s"$K.${d.name}", defCtx(d), env)._1
            val implName = name.replaceFirst("^(eval|probe)_", "$1Impl_")
            Eval(implName, s"$label, run by ${d.name}", s"$f $ta $tb = $tg", s"$f $ta $tb ≠ $tg")
          onPost.toList ++ onImpl.toList
      val out = n.cases.zipWithIndex.map { (e, i) =>
        val label = s"example ${i + 1} (${e.note})"
        one(s"eval_$i", label, e.bindings, e.a, e.b, Some(e.result)).left.map(why => (s"eval_$i", s"$label: $why"))
      }
      // Probes: with the first example's bindings, inputs near the examples' that no example has.
      val probes = n.cases.headOption.toList.flatMap { first =>
        val nums = n.cases.flatMap(e => Generate.numbers(e.a) ++ Generate.numbers(e.b)).distinct
        val asked = n.cases.map(e => (e.a, e.b)).toSet
        val inputs = n.cases.flatMap(e => for { a <- e.a :: Generate.near(e.a, nums); b <- e.b :: Generate.near(e.b, nums) } yield (a, b))
          .distinct.filterNot(asked)
        // Without code to run, the post is judged on the examples' results.
        val cands = if impl.isDefined then inputs.map((a, b) => (a, b, None)) else inputs.flatMap((a, b) => n.cases.map(_.result).distinct.map(r => (a, b, Some(r))))
        // Half at a boundary (a number of one input equal to one of the other, where `<` and `<=` part),
        // half anywhere.
        val (edge, rest) = scala.util.Random(n.id.hashCode).shuffle(cands)
          .partition((a, b, _) => Generate.numbers(a).toSet.intersect(Generate.numbers(b).toSet).nonEmpty)
        edge.map(Some(_)).zipAll(rest.map(Some(_)), None, None).flatMap((x, y) => x.toList ++ y.toList).iterator.zipWithIndex
          .flatMap { case ((a, b, r), j) => one(s"probe_$j", s"probe ${j + 1}", first.bindings, a, b, r).toOption }
          .filter(_.nonEmpty).take(Generate.Probes).flatten.toList
      }
      (out.collect { case Right(es) => es }.flatten ++ probes, out.collect { case Left(w) => w })

  /** Each evaluated example, and its opposite, decided by `simp`. */
  def evalFile(n: Node[?]): Option[String] =
    val es = evals(n)._1
    Option.when(es.nonEmpty) {
      Header + s"import ${specModule(n.id)}\n" + provenImpl(n).fold("")(_ => callees(n).map(c => s"import ${specModule(c.id)}\n").mkString) + "\n" +
        Preamble + s"namespace $K.${n.id}.Eval\n\n" + es.map { e =>
        s"/-- ${e.what.replace("-/", "- /")} -/\ntheorem ${e.name} : ${e.claim} := by\n  frflow_eval\n\n" +
          s"theorem ${e.name}_opposite : ${e.opposite} := by\n  frflow_eval\n\n"
      }.mkString + s"end $K.${n.id}.Eval\n"
    }

  // ---------------------------------------------------------------------------
  // Modules of a node
  // ---------------------------------------------------------------------------

  def spec(n: Node[?]): String =
    val sb = StringBuilder()
    val imports = (s"FrFlowGen.$K.Domain" :: (kb.parts(n).filter(formal) ++ callees(n) ++ keepers(n).map(_._1)).map(c => specModule(c.id))).distinct
    sb ++= Header + imports.map(m => s"import $m\n").mkString + "\n" + Preamble
    sb ++= s"namespace $K.${n.id}\n\n"
    def d(name: String, c: Ctx, tpe: String, body: String) =
      val b = binders(c)
      sb ++= s"@[frflow_defs] def $name${if b.isEmpty then "" else " " + b} : $tpe :=\n  $body\n\n"
    def lam(name: String, l: Lifted[?]) = d(name, ctx(l), l.leanType, resolve(l.lean))
    if n.isInvariant then
      val r = n.rule.get
      lam("rule", r)
      val ks = keepers(n)
      ks.foreach((c, v) => lam(s"view_${c.id}", v))
      val rl = ref(q(n, "rule"), ctx(r))
      val conj = ks.map { (c, v) =>
        val (vars, xs) = call(c.post.get.params.init.map(_._2))
        s"(∀ $vars, ∀ p ∈ ${ref(q(n, s"view_${c.id}"), ctx(v))} $xs (${opOf(c)} $xs), $rl p.1 p.2)"
      }
      d("claim", claimCtx(n), "Prop", if conj.isEmpty then "True" else conj.mkString(" ∧ "))
    else if n.post.isDefined then
      val post = n.post.get
      lam("post", post)
      formalKeeps(n).foreach { (inv, v) => lam(s"rule_${inv.id}", inv.rule.get); lam(s"view_${inv.id}", v) }
      n.local.foreach(lam("runCheck", _))
      val (vars, xs) = call(post.params.init.map(_._2))
      d("claim", claimCtx(n), "Prop", s"∀ $vars, ${ref(q(n, "post"), ctx(post))} $xs (${opOf(n)} $xs)")
    else
      lam("claim", n.formula.get)
    n.expected.zipWithIndex.foreach { case ((_, l), i) => lam(s"expected_$i", l) }
    (obligations(n) ++ tries(n).map(_.obligation)).foreach { o =>
      sb ++= s"namespace Obl\n\n/-- ${o.description.replace("-/", "- /")} -/\n@[frflow_defs] def ${o.name} : Prop :=\n  ${o.statement}\n\nend Obl\n\n"
    }
    sb ++= s"$MatchEqns\nend $K.${n.id}\n"
    sb.result()

  /** `complete` by `frflow_auto`, unless the proof file proves it. */
  def auto(n: Node[?]): String =
    val body = obligation(n, "complete").filterNot(_ => isAuthored(n, "complete")).fold("")(o =>
      s"theorem complete : Obl.complete := by\n  unfold Obl.complete\n  frflow_auto\n\n")
    Header + s"import ${specModule(n.id)}\n\n" + Preamble + s"namespace $K.${n.id}.Auto\nopen $K.${n.id}\n\n$body" + s"end $K.${n.id}.Auto\n"

  /** `impl` by `frflow_auto`, unless the proof file proves it; with the axioms it rests on. */
  def impl(n: Node[?]): String =
    val proof = if isAuthored(n, "impl") then s"$K.${n.id}.Proofs.impl" else "by\n  unfold Obl.impl\n  frflow_auto"
    Header + s"import ${if isAuthored(n, "impl") then proofsModule(n.id) else specModule(n.id)}\n\n" + Preamble +
      s"namespace $K.${n.id}.Impl\nopen $K.${n.id}\n\ntheorem impl : Obl.impl :=\n  $proof\n\n#print axioms $K.${n.id}.Impl.impl\n\nend $K.${n.id}.Impl\n"

  /** `holds`: the node, from the leaves below it, through `complete` here and `holds` of each part. */
  def theorems(n: Node[?]): String =
    val sb = StringBuilder(Header)
    if leafy(n) then sb ++= s"import ${specModule(n.id)}\n"
    else
      sb ++= s"import ${if isAuthored(n, "complete") then proofsModule(n.id) else autoModule(n.id)}\n"
      splitParts(n).get.filterNot(leafy).foreach(c => sb ++= s"import ${theoremsModule(c.id)}\n")
    sb ++= "\n" + Preamble + s"namespace $K.${n.id}\n\n"
    val opens = holdsOpens(n)
    val intro = opens.names ++ leaves(n).map(l => s"h_${l.id}")
    val proof =
      if leafy(n) then s"h_${n.id}"
      else
        val ps = splitParts(n).get
        val ref = q(n, if isAuthored(n, "complete") then "Proofs.complete" else "Auto.complete")
        s"$ref ${named(splitOpens(n, ps))} ${ps.map(c => s"(h_${c.id} := ${proofOf(c)})").mkString(" ")}"
    sb ++= s"/-- ${n.id} holds of every world that meets the leaves below it: ${leaves(n).map(_.id).mkString(", ")}. -/\n"
    sb ++= s"theorem holds : ${holdsStatement(n)} := by\n${if intro.isEmpty then "" else s"  intro ${intro.mkString(" ")}\n"}  exact $proof\n\nend $K.${n.id}\n"
    sb.result()

  /** Everything else checked of a node, in one file elaborated (not built): the obligations besides
    * `complete` and `impl` (by `frflow_auto`, or the theorem of that name in its proof file), the tries
    * (each with a small budget: they are one-sided), and the axioms `holds` rests on. Each theorem
    * stands or falls on its own; Lean goes on past one that fails.
    */
  def checks(n: Node[?]): String =
    val ns = s"$K.${n.id}.Checks"
    val sb = StringBuilder(Header + s"import ${theoremsModule(n.id)}\n")
    if extraObligations(n).exists(o => isAuthored(n, o.name)) then sb ++= s"import ${proofsModule(n.id)}\n"
    sb ++= "\n" + Preamble + s"namespace $ns\nopen $K.${n.id}\n\n"
    def auto(o: String) = s"by\n  unfold Obl.$o\n  frflow_auto"
    extraObligations(n).foreach { o =>
      sb ++= s"theorem ${o.name} : Obl.${o.name} := ${if isAuthored(n, o.name) then s"$K.${n.id}.Proofs.${o.name}" else auto(o.name)}\n\n#print axioms $ns.${o.name}\n\n"
    }
    tries(n).foreach(t => sb ++= s"set_option maxHeartbeats ${TryHeartbeats} in\ntheorem ${t.obligation.name} : Obl.${t.obligation.name} := ${auto(t.obligation.name)}\n\n")
    sb ++= s"#print axioms $K.${n.id}.holds\n\nend $ns\n"
    sb.result()

  /** Obligations proven in the Checks file: all but `complete` and `impl`. */
  def extraObligations(n: Node[?]): List[Obligation] = obligations(n).filterNot(o => o.name == "complete" || o.name == "impl")

  /** A stub for each obligation, to prove in its place. */
  def stubs(names: List[String]): String =
    names.map(o => s"theorem $o : Obl.$o := by\n  unfold Obl.$o\n  sorry\n\n").mkString

  /** A proof file with a stub for each of `names` (and for `feasible` with `complete`, unless a proven
    * implementation below witnesses the node).
    */
  def proofFile(n: Node[?], names: List[String] = List("complete")): String =
    val all = names ++ Option.when(names.contains("complete") && !witnessed(n) && !names.contains("feasible"))("feasible")
    s"""import ${specModule(n.id)}
       |
       |/-! Authored proofs of the obligations of ${n.id}. Each states exactly its `Obl`. -/
       |
       |$Preamble
       |namespace $K.${n.id}.Proofs
       |open $K.${n.id}
       |
       |${stubs(all)}end $K.${n.id}.Proofs
       |""".stripMargin

  def lakefile(kernelPath: String): String =
    s"""name = "${K.toLowerCase}"
       |defaultTargets = ["FrFlowGen"]
       |
       |[[require]]
       |name = "frflow"
       |path = "$kernelPath"
       |
       |[[lean_lib]]
       |name = "FrFlowGen"
       |globs = ["FrFlowGen.+"]
       |
       |[[lean_lib]]
       |name = "Proofs"
       |globs = ["Proofs.+"]
       |""".stripMargin
