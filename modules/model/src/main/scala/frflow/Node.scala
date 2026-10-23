package frflow

import frflow.protocol.NodeKind

/** How a node stands to an invariant: kept, through a view of each call, or exempt. */
final case class Keep(invariant: Node[?], view: Option[Lifted[?]], exempt: String = ""):
  def describe: String = view.fold(s"${invariant.id}: exempt, because ${exempt}")(v => s"${invariant.id}: ${v.source}")

  // The casts are where the untyped IR meets the values: `keeps` built the view and the rule with these types.
  private[frflow] def brokenBy(a: Any, b: Any, r: Any): Boolean =
    view.exists { v =>
      invariant.rule.exists { rl =>
        val rule = rl.value.asInstanceOf[(Any, Any) => Boolean]
        v.value.asInstanceOf[(Any, Any, Any) => List[(Any, Any)]](a, b, r).exists((x, y) => !rule(x, y))
      }
    }

/** One statement in the developer's domain words, decided by them and proven in Lean from its parts (the nodes
  * that name it `under`). `M` is the operation's type, so examples and checks are typed.
  */
final class Node[M] @scala.annotation.publicInBinary private[frflow] (val id: String, val statement: String, val why: String,
    val kind: NodeKind, val declaredParents: List[Node[?]] = Nil, val formula: Option[Lifted[?]] = None,
    val post: Option[Lifted[?]] = None, val op: Option[Param[?]] = None, val rule: Option[Lifted[?]] = None,
    val substs: List[Subst] = Nil, val cases: List[Example] = Nil, val governs: List[String] = Nil, val kept: List[Keep] = Nil,
    val scope: List[Node[?]] = Nil, val ideaSection: String = "", val file: String = "", val expected: List[(String, Lifted[?])] = Nil,
    val at: Int = -1, val local: Option[Lifted[?]] = None, val replaced: Option[Node[?]] = None):
  def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _) => i }).distinctBy(System.identityHashCode)
  def isInvariant: Boolean = rule.isDefined
  def shownKind: String = kind.shown(isInvariant)
  def defines: List[String] = substs.map(_.name)
  def referenced: List[Lifted[?]] = formula.toList ++ post.toList ++ rule.toList ++ local.toList ++ substs.flatMap(_.term) ++
    kept.flatMap(_.view) ++ expected.map(_._2)

  // `require` in the builders: a node built from one declared after it gets `null` (Scala initializes vals in
  // order), and failing as the model loads, naming the node, is what the developer can act on.

  /** A part of each of `ps`: with its co-parts, it refines each. */
  def under(ps: Node[?]*): Node[M] =
    require(ps.forall(_ != null), s"$id is under a node declared after it: declare the parent first")
    require(kind != NodeKind.Definition, s"$id: a definition has no parents; the nodes that use its terms rest on it")
    copy(declaredParents = declaredParents ++ ps)

  /** An alternative to `other`: accepting one rejects the other. */
  def replaces(other: Node[?]): Node[M] =
    require(other != null, s"$id replaces a node declared after it: declare it first")
    copy(replaced = Some(other))

  /** A consequence the developer expects, which Lean proves from the claim: "Acme never sees Globex's contact". */
  inline def expects(statement: String)(inline consequence: Boolean): Node[M] =
    copy(expected = expected :+ (statement -> Lifted(() => consequence)))

  private[frflow] def copy(declaredParents: List[Node[?]] = declaredParents, cases: List[Example] = cases, kept: List[Keep] = kept,
      expected: List[(String, Lifted[?])] = expected, local: Option[Lifted[?]] = local, replaced: Option[Node[?]] = replaced): Node[M] =
    Node(id, statement, why, kind, declaredParents, formula, post, op, rule, substs, cases, governs, kept, scope, ideaSection,
      file, expected, at, local, replaced)

  /** The invariant does not apply to this contract or design decision, for the reason given (which the developer reads). */
  def exempt(invariant: Node[?], because: String): Node[M] =
    require(invariant != null, s"$id is exempt from an invariant declared after it: declare the invariant first")
    copy(kept = kept :+ Keep(invariant, None, because))
  override def toString: String = id

object Node:
  // Each is built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).

  /** With no parents, the root: the idea's purpose, stated as *exactly*, so that doing nothing does not meet it. */
  inline def claim(id: String, statement: String, why: String, idea: String = "")(inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Claim, formula = Some(Lifted(() => formula)), ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

  /** Every call `op(a, b)` meets `post(a, b, op(a, b))`: code attached to the operation is proven or checked against it. */
  inline def contract[A, B, R](op: Param[(A, B) => R])(id: String, statement: String, why: String, idea: String = "")(
      inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted(post)), op = Some(op), ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

  /** What the outside (a database, the clock) is trusted to do: code calling it is proven from it, its adapter checked. */
  def assumption[A, B, R](op: Param[(A, B) => R]): AssumptionOn[A, B, R] = AssumptionOn(op)

  /** A fact of the world, trusted; checked at run time where the terms it reads are bound, when it can be computed. */
  inline def assumption(id: String, statement: String, why: String, idea: String = "")(inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Assumption, formula = Some(Lifted(() => formula)), ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

  /** Fixes terms of the vocabulary (`User := of[UserId]`, `authorized := (u, p) => ...`): decided, not proven. */
  inline def definition(id: String, statement: String, why: String)(substs: Subst*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Definition, substs = substs.toList, file = Lifted.here, at = Lifted.at)
    node()

  /** `rule(a, b)` holds for every pair a call exposes: every contract below `scope` that can expose one keeps it or is `exempt`. */
  inline def invariant[A, B](id: String, statement: String, why: String, scope: List[Node[?]] = Nil, idea: String = "")(
      inline rule: (A, B) => Boolean): Node[(A, B) => Boolean] =
    def node(): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Claim, rule = Some(Lifted(rule)), scope = scope, ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

  /** An architecture choice or a convention, with no formal model; a change to the files it `governs` is noticed. */
  inline def design(id: String, statement: String, why: String, idea: String = "")(governs: String*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, governs = governs.toList, ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

/** `Node.assumption(op)(id, statement, why, idea)(post)`: a step of its own, so that both assumptions default `idea`. */
final class AssumptionOn[A, B, R](val op: Param[(A, B) => R]):
  inline def apply(id: String, statement: String, why: String, idea: String = "")(
      inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Assumption, post = Some(Lifted(post)), op = Some(op), ideaSection = idea, file = Lifted.here, at = Lifted.at)
    node()

extension [A, B, R](n: Node[(A, B) => R])
  /** What `service` checks on every call instead of the post: Lean proves the post implies it, so it refuses nothing allowed. */
  inline def checkedBy(inline check: (A, B, R) => Boolean): Node[(A, B) => R] = n.copy(local = Some(Lifted(check)))

  /** Keeps an invariant: its rule holds for each pair `view(a, b, result)` lists (`result.map(r => (reader, r))`). */
  inline def keeps[X, Y](invariant: Node[(X, Y) => Boolean])(inline view: (A, B, R) => List[(X, Y)]): Node[(A, B) => R] =
    require(invariant != null, s"${n.id} keeps an invariant declared after it: declare the invariant first")
    n.copy(kept = n.kept :+ Keep(invariant, Some(Lifted(view))))

  /** Concrete cases, under the given parameter values: they fail when the contract or the code is not what was decided. */
  inline def examples(inline bindings: Binding*)(inline cases: Case[A, B, R]*): Node[(A, B) => R] =
    // Built in a method of its own (a file's top-level vals initialize in one JVM method of at most 64 KB).
    def exampleList(): List[Example] =
      cases.toList.map(c => Example(c.note, bindings.toList, Lifted.sources(bindings*), c.a, c.b, c.result, c.expected))
    n.copy(cases = n.cases ++ exampleList())
