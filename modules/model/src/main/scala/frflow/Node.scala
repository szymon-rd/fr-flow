package frflow

/** What a node is (see docs/DAG.md §2). */
enum NodeKind:
  /** A proposition over the vocabulary, in the domain's words. The one claim without parents is the
    * root: the idea's purpose. A claim with parts is proven from them; an invariant is a claim whose
    * parts are the contracts that keep it.
    */
  case Claim
  /** Every call of an operation meets a post; code attached to the operation is proven or checked
    * against it.
    */
  case Contract
  /** Trusted, not proven: what the outside does on an operation (a database, a clock), or a fact of
    * the world. A hypothesis of `root_impl`.
    */
  case Assumption
  /** Fixes terms of the vocabulary (a type, a term by an expression); decided, not proven. */
  case Definition
  /** Governs code no proof covers (an architecture choice, a convention); decided and tracked. */
  case Design

/** How a node stands to an invariant: kept, through a view of each call, or exempt. */
final case class Keep(invariant: Node[?], view: Option[Lifted[?]], exempt: String = ""):
  def describe: String = view.fold(s"${invariant.id}: exempt, because ${exempt}")(v => s"${invariant.id}: ${v.source}")

  /** Whether the call `(a, b)` returning `r` exposes a pair the invariant's rule refuses. (The casts
    * are where the untyped IR meets the values: `keeps` built the view and the rule with these types.)
    */
  private[frflow] def brokenBy(a: Any, b: Any, r: Any): Boolean =
    view.exists { v =>
      invariant.rule.exists { rl =>
        val rule = rl.value.asInstanceOf[(Any, Any) => Boolean]
        v.value.asInstanceOf[(Any, Any, Any) => List[(Any, Any)]](a, b, r).exists((x, y) => !rule(x, y))
      }
    }

/** A node of the knowledge base: one statement, in the developer's domain words, decided by the
  * developer and (when formal) proven in Lean from its parts. `M` is the operation's type for a
  * contract or an assumption on an operation (so examples and checks are typed), the rule's type for an
  * invariant, `Unit` otherwise.
  *
  * Edges point up: a node names its parents (`under`); its parts are the nodes that name it.
  */
final class Node[M] @scala.annotation.publicInBinary private[frflow] (
    val id: String,
    val statement: String,
    val why: String,
    val kind: NodeKind,
    val declaredParents: List[Node[?]] = Nil,
    /** A claim's or a fact assumption's proposition, as `() => Boolean`. */
    val formula: Option[Lifted[?]] = None,
    /** A contract's or an operation assumption's `(a, b, result) => Boolean`. */
    val post: Option[Lifted[?]] = None,
    /** The operation a contract or an assumption is about. */
    val op: Option[Param[?]] = None,
    /** An invariant's rule over pairs. */
    val rule: Option[Lifted[?]] = None,
    /** What a definition fixes. */
    val substs: List[Subst] = Nil,
    val cases: List[Example] = Nil,
    val governs: List[String] = Nil,
    val declaredFormal: Boolean = true,
    val kept: List[Keep] = Nil,
    val scope: List[Node[?]] = Nil,
    val ideaSection: String = "",
    val file: String = "",
    val expected: List[(String, Lifted[?])] = Nil,
    val at: Int = -1,
    val local: Option[Lifted[?]] = None,
    val replaced: Option[Node[?]] = None
):
  /** The nodes it is a part of: those named with `under`, and the invariants it keeps. */
  def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _) => i }).distinctBy(System.identityHashCode)

  /** A cross-cutting rule (`Node.invariant`): a claim whose parts are the contracts that keep it. */
  def isInvariant: Boolean = rule.isDefined

  /** Whether Lean checks this node (`formal = false` opts out: decided by reading). */
  def formal: Boolean = declaredFormal

  /** The terms a definition fixes. */
  def defines: List[String] = substs.map(_.name)

  /** The parts translated to Lean; none when the node is out of Lean. */
  def lifted: List[Lifted[?]] = if !formal then Nil else referenced

  /** The node's lambdas, translated or not: what it refers to (definitions, parameters, opaque types)
    * is known either way, so a change to them reaches it.
    */
  def referenced: List[Lifted[?]] = formula.toList ++ post.toList ++ rule.toList ++ local.toList ++ substs.flatMap(_.term) ++
    kept.flatMap(_.view) ++ expected.map(_._2)

  // `require` in the builders: a node built from one declared after it gets `null` (Scala initializes
  // vals in order), and failing as the model loads, naming the node, is what the developer can act on.

  /** This node is a part of each of `ps`: together with its co-parts, it refines each. */
  def under(ps: Node[?]*): Node[M] =
    require(ps.forall(_ != null), s"$id is under a node declared after it: declare the parent first")
    require(kind != NodeKind.Definition, s"$id: a definition has no parents; the nodes that use its terms rest on it")
    copy(declaredParents = declaredParents ++ ps)

  /** An alternative to `other`: accepting one rejects the other. */
  def replaces(other: Node[?]): Node[M] =
    require(other != null, s"$id replaces a node declared after it: declare it first")
    copy(replaced = Some(other))

  /** A consequence the developer expects of this node, stated as a check of their understanding (Lean
    * proves it from the node's claim): "Acme never sees Globex's unshared contact".
    */
  inline def expects(statement: String)(inline consequence: Boolean): Node[M] =
    copy(expected = expected :+ (statement -> Lifted.of(true, () => consequence)))

  private[frflow] def copy(declaredParents: List[Node[?]] = declaredParents, cases: List[Example] = cases, kept: List[Keep] = kept,
      expected: List[(String, Lifted[?])] = expected, local: Option[Lifted[?]] = local, replaced: Option[Node[?]] = replaced): Node[M] =
    Node(id, statement, why, kind, declaredParents, formula, post, op, rule, substs, cases, governs, declaredFormal, kept, scope, ideaSection,
      file, expected, at, local, replaced)

  private[frflow] def withExamples(es: List[Example]): Node[M] = copy(cases = cases ++ es)
  private[frflow] def withKeeps(ks: List[Keep]): Node[M] = copy(kept = ks)
  private[frflow] def withLocal(l: Lifted[?]): Node[M] = copy(local = Some(l))

  /** The invariant does not apply to this contract or design decision, for the reason given (part of
    * what the node says, so the developer reads it).
    */
  def exempt(invariant: Node[?], because: String): Node[M] =
    require(invariant != null, s"$id is exempt from an invariant declared after it: declare the invariant first")
    withKeeps(kept :+ Keep(invariant, None, because))

  override def toString: String = id

object Node:
  // Each is built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).

  /** A claim: a proposition over the vocabulary. With no parents, it is the root: the idea's purpose,
    * stated as *exactly* (what users can do and what must never happen), so that doing nothing does not
    * meet it. `idea` names the section of IDEA.md it is decided against.
    */
  inline def claim(id: String, statement: String, why: String, idea: String = "", inline formal: Boolean = true)(
      inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Claim, formula = Some(Lifted.of(formal, () => formula)), declaredFormal = formal, ideaSection = idea,
        file = Lifted.here, at = Lifted.at)
    node()

  /** A contract on an operation: every call `op(a, b)` meets `post(a, b, op(a, b))`. Code attached to the
    * operation (`KnowledgeBase.implementProven`, `implement`) is proven or checked against it.
    */
  inline def contract[A, B, R](op: Param[(A, B) => R])(id: String, statement: String, why: String, idea: String = "",
      inline formal: Boolean = true)(inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.of(formal, post)), op = Some(op), declaredFormal = formal,
        ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

  /** What the outside is trusted to do on an operation (a database, an HTTP service, the clock): not
    * proven, a hypothesis of `root_impl`. Code calling the operation is proven from it; its adapter is
    * checked against it at run time (give it a cheap `checkedBy`).
    */
  def assumption[A, B, R](op: Param[(A, B) => R]): AssumptionOn[A, B, R] = AssumptionOn(op)

  /** A fact of the world, trusted (a hypothesis of `root_impl`); checked at run time wherever the
    * terms it reads are bound, when it can be computed.
    */
  inline def assumption(id: String, statement: String, why: String, idea: String = "")(inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Assumption, formula = Some(Lifted.of(true, () => formula)), ideaSection = idea,
        file = Lifted.here, at = Lifted.at)
    node()

  /** Fixes terms of the vocabulary: `User := of[UserId]`, `authorized := (u, p) => ...`. Decided, not
    * proven; the nodes whose statements mention a term it defines rest on it.
    */
  inline def definition(id: String, statement: String, why: String)(substs: Subst*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Definition, substs = substs.toList, file = Lifted.here, at = Lifted.at)
    node()

  /** A cross-cutting invariant: `rule(a, b)` holds for every pair a call exposes (such as a reader and a
    * record returned to them), stated once. It is a claim whose parts are the contracts that keep it
    * (`keeps`); every contract below the `scope` nodes (anywhere, when none are given) whose result can
    * hold what the rule is about keeps it or is `exempt`.
    */
  inline def invariant[A, B](id: String, statement: String, why: String, scope: List[Node[?]] = Nil, idea: String = "",
      inline formal: Boolean = true)(inline rule: (A, B) => Boolean): Node[(A, B) => Boolean] =
    def node(): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Claim, rule = Some(Lifted.of(formal, rule)), declaredFormal = formal, scope = scope, ideaSection = idea,
        file = Lifted.here, at = Lifted.at)
    node()

  /** A design decision with no formal model: an architecture choice or a convention, under the nodes
    * it serves. `governs` are the source files it is about, so a change to them is noticed.
    */
  inline def design(id: String, statement: String, why: String, idea: String = "")(governs: String*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, governs = governs.toList, ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

/** `Node.assumption(op)(id, statement, why, idea)(post)`: an assumption on an operation. (A step of
  * its own, so that it and the assumption on a fact both take `idea` with a default.)
  */
final class AssumptionOn[A, B, R](val op: Param[(A, B) => R]):
  inline def apply(id: String, statement: String, why: String, idea: String = "")(
      inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Assumption, post = Some(Lifted.of(true, post)), op = Some(op), ideaSection = idea,
        file = Lifted.here, at = Lifted.at)
    node()

/** The builders of a contract or an assumption on an operation. */
extension [A, B, R](n: Node[(A, B) => R])
  /** What `service` checks on every call instead of the whole post: a check of the result alone (each
    * returned row matches the query, say), cheap where the post reads all the data. Lean proves the
    * post implies it, so it refuses nothing the contract allows; what it leaves out (that nothing is
    * missing) rests on the proofs, and on the assumption's promise.
    */
  inline def checkedBy(inline check: (A, B, R) => Boolean): Node[(A, B) => R] = n.withLocal(Lifted.of(true, check))

  /** This contract keeps an invariant: `view(a, b, result)` lists the pairs the call exposes to it
    * (such as `result.map(r => (reader, r))`), and the invariant's rule holds for each. It makes the
    * contract a part of the invariant; it is also checked on the examples and at run time.
    */
  inline def keeps[X, Y](invariant: Node[(X, Y) => Boolean], inline formal: Boolean = true)(
      inline view: (A, B, R) => List[(X, Y)]): Node[(A, B) => R] =
    require(invariant != null, s"${n.id} keeps an invariant declared after it: declare the invariant first")
    n.withKeeps(n.kept :+ Keep(invariant, Some(Lifted.of(formal, view))))

  /** Concrete cases of the contract, under the given parameter values. They show what
    * the contract means, and they fail when it is vacuous, too weak, or when the
    * implementation does not do what was decided.
    */
  inline def examples(inline bindings: Binding*)(inline cases: Case[A, B, R]*): Node[(A, B) => R] =
    // Built in a method of its own (a file's top-level vals initialize in one JVM method of at most 64 KB).
    def exampleList(): List[Example] =
      cases.toList.map(c => Example(c.note, bindings.toList, Lifted.sources(bindings*), c.a, c.b, c.result, c.expected))
    n.withExamples(exampleList())
