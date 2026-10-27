package frflow
package lean

import frflow.kb.Reach
import frflow.protocol.NodeKind

/** How the nodes refine each other in Lean: their claims and splits, their proven code, `holds` and `root_impl`. */
final class Refinement(kb: FrModel, val vocabulary: Vocabulary):
  import vocabulary.*
  private val K = kb.name
  def formal(n: Node[?]): Boolean = kb.isStatement(n)
  /** An `always` claim has no step: its premises are what its proofs (`kept_by_…`, `initially`) take, not parts. Nor
    * is one a part of a step: what it says is a hypothesis of every statement about what it is about (`assumed`),
    * the step's own among them, and it is proven by its own obligations.
    */
  def splitParts(n: Node[?]): Option[List[Node[?]]] =
    Option.when(formal(n) && !n.isAlways)(kb.parts(n).filterNot(Refinement.isRule)).filter(_.nonEmpty)
  def leafy(n: Node[?]): Boolean = splitParts(n).isEmpty
  def formalKeeps(n: Node[?]): List[(Node[?], Lifted[?])] =
    if n.kind != NodeKind.Contract then Nil else n.kept.collect { case Keep(i, Some(v), _) if i.rule.isDefined => (i, v) }
  def keepers(i: Node[?]): List[(Node[?], Lifted[?])] =
    kb.nodes.flatMap(c => formalKeeps(c).filter(_._1 eq i).map(k => (c, k._2)))
  def provenImpl(n: Node[?]): Option[Def[?]] =
    if !formal(n) || n.op.isEmpty then None else kb.implementation(n).flatMap(_.proven)
  def qualified(n: Node[?], decl: String): String = s"$K.${n.id}.$decl"
  private def opLeaf(n: Node[?]): Ctx = n.op.fold(Ctx.empty)(o => leaf(o.name))

  /** What an invariant of a type gives of `x`, of Lean type `t`: its rule, where it reaches; of a world, what always
    * holds of what its models hold.
    */
  def assumed(x: String, t: String): List[String] =
    if t == "World" then worldAssumed(x) else kb.invariantsOn(t).map((_, d, r) => ruleOf(d, x, r))
  /** The rule `d` of `x`, where it reaches: of it, of each of its elements, or within its fields. */
  def ruleOf(d: Def[?], x: String, reach: Reach): String = reach.lean(x, app(s"$K.${d.name}", defCtx(d))._1)
  /** What always holds of the states the models hold in world `w`: their types' rules, and their stores'. */
  def worldAssumed(w: String): List[String] =
    kb.models.flatMap(m => kb.worldRules(m).map((_, d, r) => ruleOf(d, s"$w.${m.model.field}", r)))
  private def invariantsCtx(n: Node[?]): Ctx = Ctx.all(kb.invariantsUsedBy(n).flatMap(_.holds).map(defCtx))

  /** An `always` claim says nothing Lean proves of every value: a hypothesis of the others, it is proven kept. */
  def claimCtx(n: Node[?]): Ctx = if n.isAlways then Ctx.empty else invariantsCtx(n) ++ ((n.rule, n.post) match
    case (Some(r), _) => ctx(r) ++ Ctx.all(keepers(n).map((c, v) => ctx(v) ++ opLeaf(c)))
    case (_, Some(p)) => ctx(p) ++ opLeaf(n)
    case _            => n.formula.fold(Ctx.empty)(ctx(_)))
  def claim(n: Node[?], env: Env = Map.empty): (String, Ctx) =
    app(qualified(n, "claim"), claimCtx(n), mentioned(n) ++ env)
  /** In a statement saying what a Declaration is in the code's words (`accepted(request, now) ===
    * book(…).answer(now)`), proven code stands for each Definition it mentions: the Declaration is what that code
    * does, and is witnessed by it. Other statements hold for every meaning their parts allow.
    */
  private def mentioned(n: Node[?]): Env =
    if !isMeaning(n) then Map.empty
    else
      val own = n.op.map(_.name).toSet
      val named = claimCtx(n).params.toSet
      codeEnv.filter((op, _) => named(op) && !own(op))
  /** The proven code that stands for what a statement mentions (`mentioned`): its Lean needs those definitions. */
  def mentionedCode(n: Node[?]): List[Def[?]] =
    val texts = mentioned(n).values.map(_._1).mkString(" ")
    def byName(d: Def[?]) = s"(?<![\\w.'])${java.util.regex.Pattern.quote(s"$K.${d.name}")}(?![\\w'])".r
    implemented.map(_._2).distinctBy(_.name).filter(d => byName(d).findFirstIn(texts).isDefined)
  /** What a node's parts make: its claim, or, for a contract whose proven code its parts are about (a root stated of
    * the service's flow), its claim of that code: the parts state what the code calls, not the operation itself.
    */
  def stepClaim(n: Node[?], env: Env = Map.empty): (String, Ctx) =
    val code = for
      d <- provenImpl(n) if kb.parts(n).nonEmpty
      op <- n.op if !env.contains(op.name)
    yield op.name -> this.code(d, env)
    claim(n, env ++ code)
  /** Whether the node's step is proven of its code (`stepClaim`). */
  def ofCodeStep(n: Node[?]): Boolean = provenImpl(n).isDefined && kb.parts(n).nonEmpty
  /** A claim's top-level conjuncts (in Lean), when it has as many as its parts, two or more: then a part may only restate
    * one of them with the definitions applied, which `restates_<i>_<part>` tries. None otherwise.
    */
  def conjunctsOf(n: Node[?]): List[String] =
    (for
      l <- n.formula if n.rule.isEmpty && n.post.isEmpty && l.params.isEmpty
      ps <- splitParts(n) if ps.size >= 2
      cs = LeanText.conjuncts(l.body) if cs.size == ps.size
    yield cs).getOrElse(Nil)
  /** Conjunct `i` (from 1) of the claim, applied as the claim is. */
  def conjunct(n: Node[?], i: Int): (String, Ctx) = app(qualified(n, s"conjunct_$i"), claimCtx(n))
  def hyps(ns: List[Node[?]], env: Env = Map.empty): List[((String, String), Ctx)] =
    ns.map(c => { val (t, o) = claim(c, env); ((s"h_${c.id}", t), o) })
  /** The parts as hypotheses of a step: what each one's own parts make. */
  def partHyps(ps: List[Node[?]]): List[((String, String), Ctx)] =
    ps.map(c => { val (t, o) = stepClaim(c); ((s"h_${c.id}", t), o) })
  def splitOpens(n: Node[?], parts: List[Node[?]]): Ctx = stepClaim(n)._2 ++ Ctx.all(partHyps(parts).map(_._2))
  def code(d: Def[?], env: Env = Map.empty): (String, Ctx) = app(s"$K.${d.name}", defCtx(d), env)
  private def onOps(n: Node[?], ops: List[String]): List[Node[?]] =
    ops.filterNot(n.op.map(_.name).contains).flatMap(p => kb.onOp.getOrElse(p, Nil)).filter(formal).distinct
  /** Whose operations the node's code reads, also through defined terms: composed before it in `root_impl`. */
  def callees(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => code(d)._2.params))
  /** The callees a node's meaning rests on: all but those that fix a word left open above (`leftOpenAbove`) whose
    * operation its statement names. Such a statement holds whatever the operation does, so a change to that contract
    * moves only the Lean check of the code, not what the developer decided. Nor those below it: a node whose code is
    * made from its parts rests on them, and they are decided after it.
    */
  def reliedOn(n: Node[?]): List[Node[?]] =
    val named = claimCtx(n).params.toSet
    val below = within(n).drop(1).map(_.id).toSet
    callees(n).filterNot(c => (c.openAbove && c.op.exists(o => named(o.name))) || below(c.id))
  /** Whose operations the code calls: `impl`'s hypotheses (a term's definition is in the statement, not one of them). */
  def calls(n: Node[?]): List[Node[?]] = onOps(n, provenImpl(n).toList.flatMap(d => defCtx(d).params))

  def ofCode(n: Node[?], d: Def[?], op: String): (String, Ctx) =
    val (concl, co) = claim(n, Map(op -> code(d)))
    (concl, co ++ Ctx.all(hyps(calls(n)).map(_._2)))
  /** What `holds` takes as hypotheses: the leaves below a node (itself, if it is one). */
  def leaves(n: Node[?]): List[Node[?]] = splitParts(n).fold(List(n))(_.flatMap(leaves).distinctBy(_.id))
  private def within(n: Node[?]): List[Node[?]] = (n :: splitParts(n).fold(Nil)(_.flatMap(within))).distinctBy(_.id)
  /** Of every node `holds` goes through: an intermediate node may mention a term neither the node nor its leaves do. */
  def holdsOpens(n: Node[?], env: Env = Map.empty): Ctx = Ctx.all(within(n).map(stepClaim(_, env)._2))
  def holdsStatement(n: Node[?]): String = stated(holdsOpens(n), hyps(leaves(n)).map(_._1), stepClaim(n)._1)

  def proofOf(n: Node[?]): String =
    if leafy(n) then s"h_${n.id}"
    else s"(${qualified(n, LeanText.Holds)} ${named(holdsOpens(n))} ${leaves(n).map(l => s"(h_${l.id} := h_${l.id})").mkString(" ")})"
  private lazy val implemented: List[(Node[?], Def[?], String)] =
    kb.nodes.flatMap(c => for { d <- provenImpl(c) if c.onOperation; op <- c.op } yield (c, d, op.name))

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

  /** What the roots' `root_impl` assume: the assumptions, leaves and called contracts no proven code implements; not
    * the statements saying what a Declaration is, which nothing implements (they are its meaning, not trusted of code).
    */
  lazy val trusted: List[Node[?]] = kb.roots.flatMap(trustedBy).filterNot(isMeaning).distinctBy(_.id)
  /** What one root's `root_impl` assumes. */
  def trustedBy(root: Node[?]): List[Node[?]] =
    Option.when(formal(root) && !root.isAlways)(root).toList.flatMap { r =>
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
      // What a Declaration is is witnessed by the consistency check: some meaning of it meets what is said of it.
      below.updated(n.id, provenImpl(n).isDefined || tested(n) || n.kind == NodeKind.Assumption ||
        (parts.isEmpty && isMeaning(n)) || (parts.nonEmpty && parts.forall(p => below.getOrElse(p.id, false))))
  private lazy val witnesses: Map[String, Boolean] = kb.nodes.foldLeft(Map.empty[String, Boolean])(witness)

  /** A claim at the bottom saying what a Declaration is (`booked(now) === storedBookings.in(now)`): a Declaration is
    * known only by such statements and never implemented, so nothing is proven of code there; some meaning of it
    * must meet them all (the consistency check).
    */
  def isMeaning(n: Node[?]): Boolean =
    n.kind == NodeKind.Claim && !n.isAlways && kb.parts(n).isEmpty &&
      (n.op.toList ++ n.referenced.flatMap(_.paramObjects)).exists(_.isInstanceOf[Declaration[?]])
  /** Plain code `check` tests against the contract: trusted in `root_impl`, as an assumption is. */
  def tested(n: Node[?]): Boolean = formal(n) && n.op.isDefined && kb.implementation(n).exists(_.proven.isEmpty)
  /** Shown to be met: by proven or tested code, an assumption, what a Declaration is (shown consistent), or parts that
    * all are (a part nothing proves witnesses nothing).
    */
  def witnessed(n: Node[?]): Boolean = witness(witnesses, n).getOrElse(n.id, false)

object Refinement:
  /** An `always` claim: proven by its own obligations, a hypothesis of the statements about what it is about. */
  def isRule(n: Node[?]): Boolean = n.kind == NodeKind.Claim && n.isAlways
