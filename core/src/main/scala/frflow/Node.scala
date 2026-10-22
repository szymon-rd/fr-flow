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

/** The source files a node governs (a contract's implementation, a design decision's files),
  * and a hash of their content, to notice when they change.
  */
final case class Code(files: List[String], fingerprint: String)

/** How a node stands to an invariant: kept, through a view of each call (with, when several inputs
  * have the rule's first type, the index of the one the pairs are about: the reader), or exempt.
  */
final case class Keep(invariant: Node[?], view: Option[Lifted[?]], exempt: String = "", reader: Int = -1):
  def describe: String = view.fold(s"${invariant.id}: exempt, because ${exempt}")(v =>
    s"${invariant.id}: ${v.source}${if reader >= 0 then s" (reader: input ${reader + 1})" else ""}")

object Code:
  /** The files under `paths` (directories are walked), named relative to `base`, so the fingerprint
    * is the same in every checkout.
    */
  def of(base: java.nio.file.Path, paths: List[java.nio.file.Path]): Code =
    import scala.jdk.CollectionConverters.*
    val files = paths.map(_.toAbsolutePath.normalize).flatMap { p =>
      if java.nio.file.Files.isDirectory(p) then java.nio.file.Files.walk(p, java.nio.file.FileVisitOption.FOLLOW_LINKS).iterator.asScala.filter(java.nio.file.Files.isRegularFile(_)).toList
      else List(p)
    }.distinct.map(p => base.toAbsolutePath.normalize.relativize(p).toString -> p).sortBy(_._1)
    val text = files.map((rel, p) => rel + "\u0000" + (if java.nio.file.Files.isRegularFile(p) then java.nio.file.Files.readString(p) else "<missing>"))
      .mkString("\u0000")
    Code(files.map(_._1), Sha(text))

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
    val owner: String = "",
    val replaced: Option[Node[?]] = None
):
  /** The nodes it is a part of: those named with `under`, and the invariants it keeps. */
  def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _, _) => i }).distinctBy(System.identityHashCode)

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
      file, expected, at, local, owner, replaced)

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
    * meet it. `idea` names the section of IDEA.md it is decided against; `owner`, who decides it.
    */
  inline def claim(id: String, statement: String, why: String, idea: String = "", owner: String = "", inline formal: Boolean = true)(
      inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Claim, formula = Some(Lifted.of(formal, () => formula)), declaredFormal = formal, ideaSection = idea,
        owner = owner, file = Lifted.here, at = Lifted.at)
    node()

  /** A contract on an operation: every call `op(a, b)` meets `post(a, b, op(a, b))`. Code attached to the
    * operation (`KnowledgeBase.implementProven`, `implement`) is proven or checked against it.
    */
  inline def contract[A, B, R](op: Param[(A, B) => R])(id: String, statement: String, why: String, idea: String = "", owner: String = "",
      inline formal: Boolean = true)(inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.of(formal, post)), op = Some(op), declaredFormal = formal,
        ideaSection = idea, owner = owner, file = Lifted.here, at = Lifted.at)
    node()

  /** What the outside is trusted to do on an operation (a database, an HTTP service, the clock): not
    * proven, a hypothesis of `root_impl`. Code calling the operation is proven from it; its adapter is
    * checked against it at run time (give it a cheap `checkedBy`).
    */
  inline def assumption[A, B, R](op: Param[(A, B) => R])(id: String, statement: String, why: String)(
      inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Assumption, post = Some(Lifted.of(true, post)), op = Some(op), file = Lifted.here, at = Lifted.at)
    node()

  /** A fact of the world, trusted (a hypothesis of `root_impl`); checked at run time wherever the
    * terms it reads are bound, when it can be computed.
    */
  inline def assumption(id: String, statement: String, why: String)(inline formula: Boolean): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Assumption, formula = Some(Lifted.of(true, () => formula)), file = Lifted.here, at = Lifted.at)
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
  inline def invariant[A, B](id: String, statement: String, why: String, scope: List[Node[?]] = Nil, idea: String = "", owner: String = "",
      inline formal: Boolean = true)(inline rule: (A, B) => Boolean): Node[(A, B) => Boolean] =
    def node(): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Claim, rule = Some(Lifted.of(formal, rule)), declaredFormal = formal, scope = scope, ideaSection = idea,
        owner = owner, file = Lifted.here, at = Lifted.at)
    node()

  /** A design decision with no formal model: an architecture choice or a convention, under the nodes
    * it serves. `governs` are the source files it is about, so a change to them is noticed.
    */
  inline def design(id: String, statement: String, why: String, idea: String = "", owner: String = "")(governs: String*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, governs = governs.toList, ideaSection = idea, owner = owner, file = Lifted.here, at = Lifted.at)
    node()

/** A concrete case of a contract, under given parameter values: the call `(a, b)`
  * with `result`. An `expect`ed case must be accepted by the contract and returned by
  * the implementation; a `reject`ed one must be refused by the contract.
  */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], a: Any, b: Any, result: Any, expected: Boolean):
  def call: String = s"(${Example.show(a)}, ${Example.show(b)}) ⇒ ${Example.show(result)}"
  /** The parameter values, as values where they print as such (functions as their source). */
  def givens: List[String] = bindings.zip(givenSource).map { (b, src) =>
    // A value prints as itself when it is data; otherwise (a function, a connection) as its source.
    def data(v: Any): Boolean = v match
      case _: String | _: Boolean | _: Int | _: Long | _: BigInt | _: Char => true
      case o: Option[?] => o.forall(data)
      case i: Iterable[?] => i.forall(data)
      case p: Product => !p.getClass.getName.contains("$$Lambda") && p.productIterator.forall(data)
      case _ => false
    val v = Bindings.within(bindings)(b.value())
    if data(v) then s"${b.param.name} = ${Example.show(v)}" else src
  }
  def describe: String = s"${if expected then "expect" else "reject"} $call  given ${givens.mkString(", ")}  — $note"

object Example:
  def memo(f: Any => Any): Any => Any =
    val seen = scala.collection.mutable.Map.empty[Any, Any]
    a => seen.getOrElseUpdate(a, f(a))

  def show(v: Any): String = v match
    case s: String => "\"" + s + "\""
    case None      => "None"
    case Some(x)   => s"Some(${show(x)})"
    case l: List[?] => l.map(show).mkString("List(", ", ", ")")
    case m: Map[?, ?] => m.map((k, x) => s"${show(k)} -> ${show(x)}").mkString("Map(", ", ", ")")
    case p: Product if p.productArity > 0 =>
      p.productPrefix + p.productIterator.map(show).mkString("(", ", ", ")")
    case other => String.valueOf(other)

/** One case of `examples`. */
final case class Case[A, B, R](a: A, b: B, result: R, expected: Boolean, note: String)

/** The contract accepts this result, and the implementation must return it. */
def expect[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, true, note)

/** The contract must refuse this result. */
def reject[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, false, note)

/** The outcome of one example: against the contract, and against the implementation if one is registered. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  /** In words: "ok", or what went wrong, of the contract and of the implementation. */
  def verdict: String =
    List(Option.when(contract != "ok")(contract), implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten match
      case Nil => "ok"
      case ws  => ws.mkString("; ")

/** Raised by an enforced implementation whose result breaks its contract. */
final class ContractViolation(node: String, detail: String) extends RuntimeException(s"$node: $detail")

extension [A, B, R](n: Node[(A, B) => R])
  /** What `service` checks on every call instead of the whole post: a check of the result alone (each
    * returned row matches the query, say), cheap where the post reads all the data. Lean proves the
    * post implies it, so it refuses nothing the contract allows; what it leaves out (that nothing is
    * missing) rests on the proofs, and on the assumption's promise.
    */
  inline def checkedBy(inline check: (A, B, R) => Boolean): Node[(A, B) => R] = n.withLocal(Lifted.of(true, check))

  /** A plain Scala implementation with every call checked against the contract: a result that
    * breaks it is never returned. Used by `KnowledgeBase.service`, which is how code is attached.
    */
  private[frflow] def enforce(impl: (A, B) => R, assumes: List[Assumption] = Nil)(bindings: Binding*): (A, B) => R =
    require(n.post.isDefined, s"${n.id} is not a contract")
    // The cheap check when the contract gives one (Lean proves the post implies it), else the post.
    val check = n.local.getOrElse(n.post.get).value.asInstanceOf[(A, B, R) => Boolean]
    val what = if n.local.isDefined then "its check" else "the contract"
    // What each assumption was last found to hold of: checked again when a value it reads changes.
    val held = java.util.concurrent.ConcurrentHashMap[String, List[Any]]()
    (a, b) =>
      // Each parameter is read once per call, and only if something reads it (a whole table a cheap
      // check does not read is never loaded): the implementation and the check see the same values.
      val cells = bindings.map(b => b.param.name -> Cell(b)).toMap
      Bindings.within(cells.values.map(c => Binding(c.binding.param, () => c.get)).toSeq) {
        val r = impl(a, b)
        if !check(a, b, r) then throw ContractViolation(n.id, s"result $r for ($a, $b) breaks $what")
        n.broken(a, b, r).foreach(i => throw ContractViolation(n.id, s"result $r for ($a, $b) breaks the invariant $i"))
        assumes.filter(x => x.reads.forall(p => cells.get(p).exists(_.loaded))).foreach { x =>
          val vs = x.reads.toList.sorted.map(cells(_).get)
          val last = held.get(x.what)
          if last == null || last.size != vs.size || last.zip(vs).exists((p, q) => !(p.asInstanceOf[AnyRef] eq q.asInstanceOf[AnyRef])) then
            if !x.holds() then throw ContractViolation(n.id, s"the values it runs with break the assumption ${x.what}")
            held.put(x.what, vs)
        }
        r
      }

  /** This contract keeps an invariant: `view(a, b, result)` lists the pairs the call exposes to it
    * (such as `result.map(r => (reader, r))`), and the invariant's rule holds for each. It makes the
    * contract a part of the invariant; it is also checked on the examples and at run time.
    */
  inline def keeps[X, Y](invariant: Node[(X, Y) => Boolean], inline formal: Boolean = true, reader: Int = -1)(
      inline view: (A, B, R) => List[(X, Y)]): Node[(A, B) => R] =
    require(invariant != null, s"${n.id} keeps an invariant declared after it: declare the invariant first")
    n.withKeeps(n.kept :+ Keep(invariant, Some(Lifted.of(formal, view)), reader = reader))

  /** The first invariant a call's result breaks, if any. */
  def broken(a: A, b: B, r: R): Option[String] =
    n.kept.find { k =>
      k.view.exists { v =>
        val rule = k.invariant.rule.get.value.asInstanceOf[(Any, Any) => Boolean]
        v.value.asInstanceOf[(A, B, R) => List[(Any, Any)]](a, b, r).exists((x, y) => !rule(x, y))
      }
    }.map(_.invariant.id)

  /** Concrete cases of the contract, under the given parameter values. They show what
    * the contract means, and they fail when it is vacuous, too weak, or when the
    * implementation does not do what was decided.
    */
  inline def examples(inline bindings: Binding*)(inline cases: Case[A, B, R]*): Node[(A, B) => R] =
    // Built in a method of its own (a file's top-level vals initialize in one JVM method of at most 64 KB).
    def exampleList(): List[Example] =
      cases.toList.map(c => Example(c.note, bindings.toList, Lifted.sources(bindings*), c.a, c.b, c.result, c.expected))
    n.withExamples(exampleList())

  /** Each example, checked against the contract and, if given, against an implementation
    * built under the example's parameter values.
    */
  def checkExamples(impl: Option[() => (A, B) => R], assumes: List[Assumption] = Nil): List[ExampleResult] =
    val post = n.post.get.value.asInstanceOf[(A, B, R) => Boolean]
    def attempt(f: => String) = try f catch case e: Exception => s"error: ${e.getMessage}"
    // The implementation is built once per set of given values, as a running system would be.
    val built = scala.collection.mutable.Map.empty[List[Binding], Option[(A, B) => R]]
    n.cases.map { e =>
      val (a, b, r) = (e.a.asInstanceOf[A], e.b.asInstanceOf[B], e.result.asInstanceOf[R])
      Bindings.within(e.bindings) {
        val c = attempt {
          val ok = post(a, b, r)
          val broken = assumes.find(x => x.reads.forall(p => e.bindings.exists(_.param.name == p)) && !x.holds())
          if broken.isDefined then s"the values it gives break the assumption ${broken.get.what}"
          else if ok != e.expected then (if e.expected then "the contract refuses it" else "the contract accepts it")
          else if e.expected then n.broken(a, b, r).fold("ok")(i => s"the invariant $i refuses it")
          else "ok"
        }
        val i = impl.map(mk => attempt {
          val f = built.getOrElseUpdate(e.bindings, Some(mk())).get
          val got = f(a, b)
          n.broken(a, b, got).map(i => s"returned ${Example.show(got)}, which breaks the invariant $i")
            .getOrElse(if e.expected == (got == r) then "ok" else s"returned ${Example.show(got)}")
        })
        ExampleResult(e, c, i)
      }
    }

/** An assumption checked where code runs: its id, the parameters it reads, whether it holds now. */
final case class Assumption(what: String, reads: Set[String], holds: () => Boolean)

/** A parameter's value for one call, read when first needed (a function answers each question once). */
private[frflow] final class Cell(val binding: Binding):
  @volatile var loaded = false
  private var v: Any = null
  def get: Any = synchronized {
    if !loaded then
      def lambda(f: AnyRef) = f.getClass.getName.contains("Lambda")
      v = binding.value() match
        case f: Function1[?, ?] if lambda(f) => Example.memo(f.asInstanceOf[Any => Any])
        case f: Function2[?, ?, ?] if lambda(f) =>
          val g = f.asInstanceOf[(Any, Any) => Any]
          val m = Example.memo { case (x, y) => g(x, y) }; (x: Any, y: Any) => m((x, y))
        case f: Function3[?, ?, ?, ?] if lambda(f) =>
          val g = f.asInstanceOf[(Any, Any, Any) => Any]
          val m = Example.memo { case (x, y, z) => g(x, y, z) }; (x: Any, y: Any, z: Any) => m((x, y, z))
        case other => other
      loaded = true
    v
  }

/** An implementation registered for a contract's operation: its examples run against it, production
  * runs it through `KnowledgeBase.service`, and a change to its source files is noticed. `wiring` is the
  * source of the expression that builds it; `proven` is the `define` Lean proves meets the contract,
  * when the implementation is one.
  */
final case class Implementation(contract: String, factory: () => Any, files: List[String], wiring: String = "",
    proven: Option[Def[?]] = None):
  /** The running code is the proven `define` itself, not code checked against it (`runs`). */
  def provenCode: Boolean = proven.isDefined && wiring.isEmpty

  /** The implementation's source files; the last one listed is the model's file, where it is attached. */
  def sources: List[String] = files.dropRight(1)
  def modelFile: Option[String] = files.lastOption

/** A node another knowledge base decides: its name, the project directory (where its ledger and keys
  * are), and its idea file.
  */
final case class Imported(kb: String, root: String, idea: String)

/** A knowledge base: the developer's idea (a Markdown file) and the nodes derived from it: one root
  * claim, refined by a DAG of parts, over a shared vocabulary. `name` is the Lean namespace.
  */
final class KnowledgeBase(val name: String, val idea: String, val implementations: List[Implementation] = Nil,
    val imports: Map[String, Imported] = Map.empty)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList
  private lazy val here: Set[Int] = nodes.map(System.identityHashCode).toSet
  private def has(n: Node[?]): Boolean = here(System.identityHashCode(n))

  /** Contracts of another knowledge base this one's code calls: decided and checked there (`root`, that
    * project's directory: its ledger and keys hold their decisions). They come as leaves, without the
    * nodes above them, with the definitions their statements use and their code; here they are read, and
    * a change to one there reviews what rests on it here.
    */
  def uses(other: KnowledgeBase, root: String)(contracts: Node[?]*): KnowledgeBase =
    val brought = contracts.toList.filterNot(has)
    val defs = brought.flatMap(c => other.definitionsUsed(c, other.inForce(_ => false, fallback = true))).distinct.filterNot(has)
    val all = (brought ++ defs).distinct
    KnowledgeBase(name, idea, implementations ++ other.implementations.filter(i => brought.exists(_.id == i.contract)),
      imports ++ all.map(n => n.id -> Imported(other.name, root, other.idea)))((nodes ++ all)*)

  def node(id: String): Option[Node[?]] = nodes.find(_.id == id)

  /** A node's parents in this knowledge base (another knowledge base's node has its own parents there). */
  def parentsOf(n: Node[?]): List[Node[?]] = n.parents.filter(has)
  /** The nodes that name `n` as a parent, in the model's order: its parts, and the design decisions below it. */
  def children(n: Node[?]): List[Node[?]] = nodes.filter(c => parentsOf(c).exists(_ eq n))
  /** The parts of `n` that together refine it: claims, contracts and assumptions under it. */
  def parts(n: Node[?]): List[Node[?]] = children(n).filter(isStatement)
  def isStatement(n: Node[?]): Boolean = n.kind == NodeKind.Claim || n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption

  /** The root: the one claim with no parents. */
  def root: Option[Node[?]] = nodes.filter(n => n.kind == NodeKind.Claim && n.parents.isEmpty && !imports.contains(n.id)) match
    case List(r) => Some(r)
    case _       => None
  def definitions: List[Node[?]] = nodes.filter(_.kind == NodeKind.Definition)

  /** Every node above `n` (each once), nearest first. */
  def ancestors(n: Node[?]): List[Node[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[Int, Node[?]]
    def go(xs: List[Node[?]]): Unit = if xs.nonEmpty then
      val fresh = xs.filterNot(x => out.contains(System.identityHashCode(x)))
      fresh.foreach(x => out(System.identityHashCode(x)) = x)
      go(fresh.flatMap(parentsOf))
    go(parentsOf(n))
    out.values.toList
  /** Every part below `n`, however deep (each once). */
  def descendants(n: Node[?]): List[Node[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[Int, Node[?]]
    def go(xs: List[Node[?]]): Unit = xs.foreach { x =>
      if !out.contains(System.identityHashCode(x)) then { out(System.identityHashCode(x)) = x; go(parts(x)) } }
    go(parts(n))
    out.values.toList

  /** The contracts and assumptions about each operation, by its name. */
  lazy val onOp: Map[String, List[Node[?]]] = nodes.filter(_.op.isDefined).groupBy(_.op.get.name)
  /** Whether a term is an operation of the system: some contract or assumption is about it. */
  def isOp(name: String): Boolean = onOp.contains(name)

  /** Every term a node mentions, directly or through the `define`s it calls: opaque types and parameters
    * (and its operation), by name.
    */
  def termsOf(n: Node[?]): List[String] =
    val ls = n.referenced ++ Def.closure(n.referenced.flatMap(_.defs)).map(_.lifted)
    (ls.flatMap(_.opaques) ++ ls.flatMap(_.paramObjects.map(_.name)) ++ n.op.map(_.name).toList ++
      n.kept.filter(_.view.nonEmpty).flatMap(k => k.invariant.rule.toList.flatMap(_.opaques))).distinct

  /** The definitions of each term. */
  lazy val definitionsOf: Map[String, List[Node[?]]] = definitions.flatMap(d => d.defines.map(_ -> d)).groupMap(_._1)(_._2)

  /** The definition in force for each defined term: its only definition, or the one `chosen` among
    * several (they are alternatives, decided before the terms are used); with `fallback`, the first
    * listed when none is chosen (to run examples before the choice).
    */
  def inForce(chosen: String => Boolean, fallback: Boolean = false): Map[String, Node[?]] =
    definitionsOf.toList.flatMap { (t, ds) =>
      (if ds.size == 1 then ds else ds.filter(d => chosen(d.id)) match
        case List(d) => List(d)
        case _ if fallback => ds.take(1)
        case _ => Nil).map(t -> _)
    }.toMap

  /** The definitions in force a node depends on: those of the terms it mentions, and theirs, however nested. */
  def definitionsUsed(n: Node[?], inForce: Map[String, Node[?]]): List[Node[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Node[?]]
    def go(terms: List[String]): Unit = terms.flatMap(inForce.get).foreach { d =>
      if !out.contains(d.id) then { out(d.id) = d; go(termsOf(d)) } }
    go(termsOf(n).filterNot(n.defines.contains))
    out.values.toList

  /** Registers the implementation of a contract's operation. `impl` is built under the parameter
    * values of each example and of each production call, so it can read them (`grants.value`).
    */
  inline def implement[A, B, R](contract: Node[(A, B) => R])(inline impl: (A, B) => R): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => impl, Lifted.sourceFiles(impl), Lifted.sources(impl).mkString))

  /** Registers an implementation written as a `define`, in the Scala Lean translates: besides its
    * examples and the run-time check, Lean proves that every result it returns meets the contract, and
    * the root holds of it (`root_impl`).
    */
  inline def implementProven[A, B, R](contract: Node[(A, B) => R])(inline impl: Def[(A, B) => R]): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => impl.lifted.value, Lifted.sourceFiles(impl), "", Some(impl)))

  /** Production code (`runs`: an index, a database query) for a contract Lean proves of the `define`:
    * the code runs, and is checked against the define on every combination of the examples' inputs
    * (the same result), and against the contract on every call. The root is proven of the define.
    */
  inline def implementProven[A, B, R](contract: Node[(A, B) => R])(inline impl: Def[(A, B) => R], inline runs: (A, B) => R): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => runs, Lifted.sourceFiles(runs), Lifted.sources(runs).mkString, Some(impl)))

  def withImplementation(i: Implementation): KnowledgeBase =
    KnowledgeBase(name, idea, implementations.filterNot(_.contract == i.contract) :+ i, imports)(nodes*)

  private lazy val byContract = implementations.map(i => i.contract -> i).toMap
  def implementation(n: Node[?]): Option[Implementation] = byContract.get(n.id)

  /** The files the model is written in: those its nodes are defined in, and where implementations are
    * attached. A model may span several files; each holds only the model.
    */
  def modelFiles: List[String] = (nodes.map(_.file) ++ implementations.flatMap(_.modelFile)).filter(_.nonEmpty).distinct

  /** Each defined parameter bound to its definition (as examples and `service` run them). */
  def definitionBindings: List[Binding] =
    inForce(_ => false, fallback = true).toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t))
      .flatMap(s => s.param.zip(s.term).map((p, l) => Binding(p, () => l.value)))

  /** Each operation with registered code bound by `bind` (as examples and `service` call them). */
  private def opBindings(bind: (Node[?], Implementation) => () => Any): List[Binding] =
    onOp.toList.sortBy(_._1).flatMap((_, ns) => ns.flatMap(c => implementation(c).map(i => Binding(c.op.get, bind(c, i)))).take(1))

  /** Each operation bound to its registered code, as examples run it. */
  def opCode: List[Binding] = opBindings((_, i) => () => i.factory())

  /** The running system: the registered implementation of `contract`, reading the given parameter
    * values, with every result checked against the contract (see `enforce`). Every other operation with
    * code is bound to that code's service, every defined term to its definition, and the assumptions
    * whose terms are all bound are checked at start and whenever the values they read change.
    */
  def service[A, B, R](contract: Node[(A, B) => R])(bindings: Binding*): (A, B) => R =
    val i = implementation(contract).getOrElse(throw IllegalStateException(s"no implementation of ${contract.id}"))
    val f = i.factory.asInstanceOf[() => (A, B) => R]
    val bound = bindings.map(_.param.name).toSet
    val defined = definitionBindings.filterNot(b => bound(b.param.name))
    val calls = opBindings { (c, _) =>
      lazy val s = service(c.asInstanceOf[Node[(Any, Any) => Any]])(bindings*)
      val g = (x: Any, y: Any) => s(x, y)
      () => g
    }.filterNot(b => bound(b.param.name) || contract.op.exists(_ eq b.param))
    // Fail when wired, not on the first call: every parameter the contract or its examples read
    // must be bound (a contract that starts reading a new parameter breaks old wiring here).
    val auto = (defined ++ calls).map(_.param.name).toSet
    val needed = (contract.post.toList.flatMap(l => reads(l)) ++ contract.cases.flatMap(_.bindings.map(_.param.name))).distinct
      .filterNot(p => auto(p) || contract.op.exists(_.name == p))
    val missing = needed.filterNot(bound.contains)
    if missing.nonEmpty then
      throw IllegalStateException(s"${contract.id}: bind ${missing.mkString(", ")} (the contract reads them)")
    val all = bindings ++ defined ++ calls
    val assumes = runtimeAssumptions.filter(_.reads.subsetOf(bound))
    Bindings.within(all)(assumes.find(!_.holds())).foreach(x => throw ContractViolation(contract.id, s"the values it starts with break the assumption ${x.what}"))
    contract.enforce((a, b) => f()(a, b), assumes)(all*)

  /** The data parameters a lambda reads, through the defines it calls and the definitions of the terms it uses. */
  def reads(l: Lifted[?]): List[String] =
    val force = inForce(_ => false, fallback = true)
    def go(ps: List[String], seen: Set[String]): List[String] = ps.flatMap { p =>
      if seen(p) then Nil
      else force.get(p).flatMap(_.substs.find(_.name == p)).flatMap(_.term).fold(List(p))(t => go(paramsIn(t), seen + p))
    }
    go(paramsIn(l), Set.empty).distinct
  private def paramsIn(l: Lifted[?]): List[String] = (l.paramObjects ++ Def.closure(l.defs).flatMap(_.lifted.paramObjects)).map(_.name).distinct

  /** The assumptions of facts that can be computed, to check where code runs (a quantifier over a type
    * cannot be: such an assumption is trusted only).
    */
  def runtimeAssumptions: List[Assumption] =
    nodes.filter(n => n.kind == NodeKind.Assumption && n.formula.isDefined).map { n =>
      val f = n.formula.get.value.asInstanceOf[() => Boolean]
      Assumption(n.id, reads(n.formula.get).toSet, () => try f() catch case _: NotExecutable => true)
    }

  /** The results of a node's examples, against the implementation when one is registered. */
  def exampleResults(n: Node[?]): List[ExampleResult] =
    // An example need not bind the operations its code calls, nor the defined terms: they run as in service.
    if n.cases.isEmpty then Nil
    else Bindings.within(opCode ++ definitionBindings) { n.asInstanceOf[Node[(Any, Any) => Any]].checkExamples(implementation(n).map(_.factory.asInstanceOf[() => (Any, Any) => Any]), runtimeAssumptions) ++
      generated(n) }

  /** The contract holds for every call, not only the examples: the implementation also runs on
    * every combination of the examples' inputs, under each example's parameter values. Calls whose
    * result breaks the contract are listed as failing.
    */
  def generated(n: Node[?]): List[ExampleResult] =
    implementation(n).filter(_ => n.post.isDefined && n.cases.nonEmpty).toList.flatMap { i =>
      val post = n.post.get.value.asInstanceOf[(Any, Any, Any) => Boolean]
      val as = n.cases.map(_.a).distinct
      val bs = n.cases.map(_.b).distinct
      val known = n.cases.map(e => (e.bindings, e.a, e.b)).toSet
      // Once per set of parameter values: examples giving them in the same words are one group (a value
      // with no structural equality, a database, is never equal to another).
      val groups = n.cases.map(e => (e.bindings, e.givenSource)).distinctBy(_._2)
      // Production code beside a proven define is also run on varied data: each parameter value the
      // examples give (a stored table, say) with a row dropped, repeated or changed (`Generate.near`),
      // so a query that drops rows or reads the wrong column is found where the examples' data hides it.
      val varied = if i.proven.isEmpty || i.provenCode then Nil else
        val nums = n.cases.flatMap(e => Generate.numbers(e.a) ++ Generate.numbers(e.b)).distinct
        groups.flatMap { (bindings, src) =>
          bindings.flatMap(b => scala.util.Try(Bindings.within(bindings)(b.value())).toOption.toList
            .flatMap(v => Generate.near(v, nums ++ Generate.numbers(v)).take(8))
            .map(v2 => (bindings.map(x => if x eq b then Binding(b.param, () => v2) else x), src.map(_ + s" (${b.param.name} varied: ${Example.show(v2)})"), true)))
        }
      // On varied data, a result in another order than the define's is the same result, and data the
      // outside cannot hold (two rows with one key) is no finding.
      def same(x: Any, y: Any, loose: Boolean) = (x, y) match
        case (xs: List[?], ys: List[?]) if loose => xs.size == ys.size && xs.groupBy(identity).view.mapValues(_.size).toMap == ys.groupBy(identity).view.mapValues(_.size).toMap
        case _ => x == y
      (groups.map((b, s) => (b, s, false)) ++ varied).flatMap { (bindings, src, loose) =>
        Bindings.within(bindings) {
          val f = try Some(i.factory.asInstanceOf[() => (Any, Any) => Any]()) catch case _: Exception => None
          // Code that runs beside a proven define returns what the define returns, examples included.
          val reference = i.proven.filter(_ => !i.provenCode).map(_.lifted.value.asInstanceOf[(Any, Any) => Any])
          f.toList.flatMap { impl =>
            for a <- as; b <- bs if reference.isDefined || !known((bindings, a, b)) yield
              val (r, broken) =
                try
                  val r = impl(a, b)
                  val keeps = n.asInstanceOf[Node[(Any, Any) => Any]].broken(a, b, r)
                  val expected = reference.map(_(a, b)).filterNot(same(_, r, loose))
                  (r, if expected.isDefined then Some(s"returned ${Example.show(r)}, where the proven define returns ${Example.show(expected.get)}")
                      else if !post(a, b, r) then Some(s"returned ${Example.show(r)}, which breaks the contract")
                      else keeps.map(i => s"returned ${Example.show(r)}, which breaks the invariant $i"))
                catch case e: Exception => (null, Option.when(!loose)(s"error: ${e.getMessage}"))
              broken.map(why => ExampleResult(Example("generated from the examples' inputs: the contract holds for every call", bindings, src, a, b, r, true), "ok", Some(why)))
          }.flatten
        }
      }.distinctBy(r => (r.example.a, r.example.b, r.implementation)).take(10)
    }

  /** What a contract does not promise, found mechanically: conditions of its post about the world only,
    * inputs its post never looks at, and whether an empty result (`None`, `Nil`) satisfies it for every
    * example input. Shown next to the decision, so nobody believes a contract says more than it does.
    */
  def limits(n: Node[?]): List[String] =
    assumptions(n).map(c => s"it assumes about the world, whatever the system does: `$c`") ++ (
    if n.post.isEmpty then Nil
    else
      val post = n.post.get
      val unused = if !n.formal then Nil else post.params.init.map(_._1).filterNot(p => (s"(?<![\\w'])${java.util.regex.Pattern.quote(p)}(?![\\w'])").r.findFirstIn(post.body).isDefined)
      val f = post.value.asInstanceOf[(Any, Any, Any) => Boolean]
      val empties = n.cases.flatMap { e =>
        val empty = e.result match
          case _: Option[?] => Some(None)
          case _: List[?]   => Some(Nil)
          case _            => None
        empty.map(v => try Bindings.within(definitionBindings ++ e.bindings)(f(e.a, e.b, v)) catch case _: Exception => false)
      }
      unused.map(p => s"the result may not depend on `$p`: the contract never looks at it") ++
        (if empties.nonEmpty && empties.forall(identity) then
          List("an empty result (None or Nil) always satisfies it: it never requires the system to return anything") else Nil))

  /** Top-level conditions of a post that never mention the call: they constrain the world, not the
    * system, and can do a proof's work.
    */
  def assumptions(n: Node[?]): List[String] =
    def strip(t: String): String =
      val x = t.trim
      // Outer parentheses that wrap the whole text: the depth stays above 0 until the last character.
      val depths = x.scanLeft(0)((d, c) => if c == '(' then d + 1 else if c == ')' then d - 1 else d).drop(1)
      if x.startsWith("(") && x.endsWith(")") && depths.dropRight(1).forall(_ > 0) then strip(x.drop(1).dropRight(1)) else x
    def split(t: String): List[String] =
      val x = strip(t)
      var d = 0
      val cuts = x.indices.filter { i => val c = x(i); if c == '(' then d += 1 else if c == ')' then d -= 1; d == 0 && c == '∧' }.toList
      if cuts.isEmpty then List(x) else (-1 :: cuts).zip(cuts :+ x.length).map((a, b) => x.substring(a + 1, b)).flatMap(split)
    n.post.filter(_ => n.formal).toList.flatMap { f =>
      val names = f.params.map(_._1)
      if names.isEmpty then Nil
      else split(f.body).filterNot(c => names.exists(b => s"(?<![\\w'.])${java.util.regex.Pattern.quote(b)}(?![\\w'])".r.findFirstIn(c).isDefined))
    }

  /** The opaque types used anywhere. */
  def opaques: List[Opaque] =
    (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.opaqueObjects).++(definitions.flatMap(_.substs).map(_.target).collect { case o: Opaque => o })
      .groupBy(_.name).values.map(_.head).toList.sortBy(_.name)

  /** The contracts and design decisions an invariant applies to, below its scope (or anywhere): the
    * contracts whose result can hold what the rule is about, and the design decisions below a contract
    * that keeps it (they govern code no proof covers there, and say why it does not break it).
    */
  def inScope(i: Node[?]): List[Node[?]] =
    // What the rule is about (the second of its pairs, such as a record), as a Lean type.
    val about = i.rule.flatMap(_.params.lift(1)).map(_._2)
    // A type holds it if it names it, or names a type that holds it (a store of records).
    val uses = types.map(t => t.name -> t.uses).toMap
    def holds(t: String, seen: Set[String] = Set.empty): Boolean =
      val names = """[A-Za-z_][\w.]*""".r.findAllIn(t).toList
      about.forall(a => names.contains(a) || names.filterNot(seen).exists(n => uses.get(n).exists(u => holds(u.mkString(" "), seen + n))))
    def returnsIt(c: Node[?]) = c.post.forall(p => p.params.isEmpty || holds(p.params.last._2))
    def keeper(c: Node[?]) = c.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    def within(c: Node[?]) = i.scope.isEmpty || (c :: ancestors(c)).exists(a => i.scope.exists(_ eq a))
    // Another knowledge base's invariant is kept by its own contracts, not by this one's.
    nodes.filter(c => imports.contains(i.id) == imports.contains(c.id)).filter { c =>
      within(c) && (c.kind match
        case NodeKind.Contract => returnsIt(c)
        // A design decision governs code no proof covers: it is in scope below a contract that keeps
        // the rule, is exempt from it or returns what it is about, and with no contract above it at all.
        case NodeKind.Design   =>
          val contracts = ancestors(c).filter(_.kind == NodeKind.Contract)
          contracts.isEmpty || contracts.exists(a => keeper(a) || a.kept.exists(_.invariant eq i) || returnsIt(a))
        case _                 => false)
    }

  /** The contracts (and assumptions) whose operations a node's proven code calls. */
  def calledBy(n: Node[?]): List[Node[?]] =
    implementation(n).flatMap(_.proven).toList.flatMap(d => Def.closure(List(d)).flatMap(_.lifted.paramObjects).map(_.name))
      .distinct.filter(p => isOp(p) && !n.op.exists(_.name == p)).flatMap(onOp(_)).filterNot(_ eq n)

  /** Every node after the nodes it rests on: its parents, the definitions it uses, the contracts its code calls. */
  lazy val ordered: List[Node[?]] =
    val force = inForce(_ => false, fallback = true)
    val done = scala.collection.mutable.LinkedHashMap.empty[Int, Node[?]]
    def visit(n: Node[?], seen: Set[Int]): Unit =
      val k = System.identityHashCode(n)
      if !done.contains(k) && !seen(k) then
        (definitionsUsed(n, force) ++ parentsOf(n) ++ calledBy(n)).foreach(visit(_, seen + k))
        done(k) = n
    nodes.foreach(visit(_, Set.empty))
    done.values.toList

  /** Defined functions used anywhere, dependencies first. */
  lazy val defs: List[Def[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
    val visiting = scala.collection.mutable.Set.empty[String]
    def visit(d: Def[?]): Unit =
      if !out.contains(d.name) && !visiting(d.name) then
        visiting += d.name
        d.lifted.defs.foreach(visit)
        visiting -= d.name
        out(d.name) = d
    nodes.flatMap(_.referenced).flatMap(_.defs).foreach(visit)
    implementations.flatMap(_.proven).foreach(visit)
    out.values.toList

  /** Parameters used anywhere (operations included). */
  lazy val params: List[Param[?]] =
    ((nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.paramObjects) ++ nodes.flatMap(_.op) ++ definitions.flatMap(_.substs).flatMap(_.param))
      .groupBy(_.name).values.map(_.head).toList.sortBy(_.name)

  /** Domain types used anywhere, dependencies first. */
  lazy val types: List[TypeDecl] =
    val all = (nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.types) ++ definitions.flatMap(_.substs).flatMap(_.types)
    val byName = all.groupBy(_.name).view.mapValues(_.head).toMap
    val out = scala.collection.mutable.LinkedHashMap.empty[String, TypeDecl]
    def visit(n: String): Unit =
      if !out.contains(n) then byName.get(n).foreach { d => d.uses.foreach(visit); out(n) = d }
    all.map(_.name).distinct.foreach(visit)
    out.values.toList

  /** Structural problems; a knowledge base with problems is not checked. */
  def problems: List[String] =
    val ids = nodes.map(_.id)
    val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r
    val names = types.map(_.name) ++ defs.map(_.name)
    val local = nodes.filterNot(n => imports.contains(n.id))
    val roots = local.filter(n => n.kind == NodeKind.Claim && n.parents.isEmpty)
    // The code of each contract's operation, and the operations it calls.
    def calls(d: Def[?]): List[String] = Def.closure(List(d)).flatMap(_.lifted.paramObjects).map(_.name).filter(isOp).distinct
    // (Plain code calls an operation through its parameter: `decide.value(...)`, `decide(...)`.)
    val called = implementations.flatMap(_.proven).flatMap(calls).toSet ++
      onOp.keySet.filter(o => implementations.exists(i => s"\\b${java.util.regex.Pattern.quote(o)}\\b".r.findFirstIn(i.wiring).isDefined))
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      roots match
        case List(_) => Nil
        case Nil     => List("a root is required: one claim with no parents, the idea's purpose")
        case rs      => List(s"one root only: ${rs.map(_.id).mkString(", ")} are claims with no parents; put all but one under the nodes they help prove"),
      // What a node rests on (its parents) must not lead back to it.
      nodes.filter(n => ancestors(n).exists(_ eq n)).map(n => s"${n.id} is above itself: what it is a part of must not lead back to it"),
      local.filter(n => (n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption) && n.parents.isEmpty && !n.op.exists(o => called(o.name)))
        .map(n => s"${n.id} has no parents: a ${n.kind.toString.toLowerCase} is a part of the nodes it helps prove, unless code calls its operation"),
      local.filter(n => n.kind == NodeKind.Design && n.parents.isEmpty).map(n => s"${n.id}: a design decision is under the nodes it serves (.under)"),
      nodes.filter(n => n.kind == NodeKind.Definition && n.parents.nonEmpty).map(n => s"${n.id}: a definition has no parents"),
      nodes.filter(n => n.kind == NodeKind.Definition && n.substs.isEmpty).map(n => s"${n.id}: a definition fixes at least one term"),
      definitions.flatMap(d => d.defines.diff(d.defines.distinct).distinct.map(t => s"${d.id} defines $t twice")),
      // A term defined through itself has no meaning.
      {
        val force = inForce(_ => false, fallback = true)
        definitions.filter(d => definitionsUsed(d, force).exists(_ eq d)).map(d => s"${d.id}: its terms are defined through themselves")
      },
      definitions.flatMap(d => d.defines.filter(isOp).map(t => s"${d.id} defines $t, an operation: code implements an operation, a definition does not")),
      nodes.flatMap(n => n.parents.filter(p => !has(p) && !imports.contains(n.id)).map(p => s"${n.id}: its parent ${p.id} is not in the knowledge base")),
      // Another knowledge base's nodes are called, not refined here.
      nodes.filter(n => !imports.contains(n.id) && parentsOf(n).exists(p => imports.contains(p.id)))
        .map(n => s"${n.id} is under ${parentsOf(n).find(p => imports.contains(p.id)).get.id}, which ${imports(parentsOf(n).find(p => imports.contains(p.id)).get.id).kb} decides: call its operation instead"),
      nodes.filter(n => n.kind != NodeKind.Design && parentsOf(n).exists(_.kind == NodeKind.Design))
        .map(n => s"${n.id}: a design decision has no statement to refine; only design decisions go below it"),
      nodes.filter(n => parentsOf(n).exists(_.kind == NodeKind.Definition)).map(n => s"${n.id}: nothing is under a definition; a node uses its terms"),
      // Code that calls its own operation would be proven assuming what it proves.
      nodes.filter(c => c.op.exists(o => implementation(c).flatMap(_.proven).exists(d => calls(d).contains(o.name))))
        .map(c => s"${c.id}: its implementation calls ${c.op.get.name} itself: it cannot be proven from its own promise"),
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      ids.filter(i => i == "Lemmas" || i == "RootImpl").map(i => s"node id $i is reserved in lean/"),
      nodes.filter(_.why.trim.isEmpty).map(n => s"${n.id}: say why (the reason for this node)"),
      nodes.filter(n => n.cases.nonEmpty && n.post.isEmpty).map(n => s"${n.id}: only contracts and assumptions on an operation have examples"),
      nodes.flatMap(n => n.kept.map(_.invariant).filterNot(i => has(i) && i.isInvariant)
        .map(i => s"${n.id} keeps ${i.id}, which is not an invariant of this knowledge base")),
      nodes.filter(n => n.kept.exists(_.view.nonEmpty) && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts keep invariants"),
      nodes.filter(n => n.kept.nonEmpty && n.kind != NodeKind.Contract && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: only contracts and design decisions are exempt from invariants"),
      nodes.flatMap(n => n.kept.groupBy(_.invariant.id).collect { case (i, ks) if ks.size > 1 => s"${n.id} names $i more than once" }),
      nodes.flatMap(n => n.kept.filter(k => k.view.isEmpty && Words.tooFew(k.exempt))
        .map(k => s"${n.id}: say in a few words why ${k.invariant.id} does not apply to it")),
      nodes.filter(_.isInvariant).flatMap(i => inScope(i).filterNot(_.kept.exists(_.invariant eq i))
        .map(c => if c.kind == NodeKind.Design then s"${c.id}: say why ${i.id} does not apply to the code it governs (.exempt): a design decision in its scope does"
          else s"${c.id}: keep ${i.id} (.keeps) or say why it does not apply (.exempt): every contract in its scope does one")),
      nodes.filter(i => i.isInvariant && !imports.contains(i.id) && !nodes.exists(_.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)))
        .map(i => s"${i.id}: no contract keeps this invariant"),
      nodes.filter(_.isInvariant).flatMap(i => i.scope.filterNot(has).map(s => s"${i.id}: its scope ${s.id} is not in the knowledge base")),
      // An opaque type something says exists of, fixed to a type that holds an Int or Long: Lean's
      // integers are unbounded, so what Lean finds may not exist in Scala.
      definitions.flatMap { d =>
        d.substs.filter(_.isType).filter(s => s.types.exists(t => """:\s*(Int|Long)\b""".r.findFirstIn(t.scala).isDefined)).flatMap { s =>
          val ex = s"∃ \\([^)]*: ${java.util.regex.Pattern.quote(s.name)}\\)".r
          nodes.flatMap(_.lifted).find(l => ex.findFirstIn(l.body).isDefined).map(_ =>
            s"${d.id}: ${s.name} := ${s.lean}, whose values hold an Int or Long, but something says one exists: Lean's integers are unbounded, Scala's are not; use BigInt")
        }
      },
      // Two definitions by one name (in two packages, say) would be one in Lean: Lean would prove one
      // while Scala runs the other.
      {
        val all = scala.collection.mutable.ListBuffer.empty[Def[?]]
        def walk(d: Def[?]): Unit = if !all.exists(_ eq d) then { all += d; d.lifted.defs.foreach(walk) }
        (nodes.flatMap(_.referenced).flatMap(_.defs) ++ implementations.flatMap(_.proven)).foreach(walk)
        all.toList.groupBy(_.name).collect { case (n, ds) if ds.size > 1 =>
          s"two different definitions are named $n (in different packages, say): Lean would know only one of them; rename one" }.toList
      },
      // Two different parameters (or opaque types) with one name would be one in Lean and at run time.
      ((nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.paramObjects) ++ nodes.flatMap(_.op) ++ definitions.flatMap(_.substs).flatMap(_.param))
        .distinctBy(System.identityHashCode).groupBy(_.name)
        .collect { case (p, ps) if ps.size > 1 => s"two different parameters are named $p: ${ps.map(_.means).mkString("; ")}; rename one" }.toList.sorted,
      (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.opaqueObjects).distinctBy(System.identityHashCode).groupBy(_.name)
        .collect { case (o, os) if os.size > 1 => s"two different opaque types are named $o; rename one" }.toList.sorted,
      nodes.filter(n => n.kind == NodeKind.Contract && !(n.cases.exists(_.expected) && n.cases.exists(!_.expected)))
        .map(n => s"${n.id}: a contract needs examples: at least one expect (what it must allow) and one reject"),
      nodes.filter(_.kind == NodeKind.Contract).flatMap { n =>
        // An implementation that always returns the same value must fail some example.
        n.cases.filter(_.expected).map(_.result).distinct match
          case List(v) if !n.cases.exists(e => !e.expected && e.result == v) =>
            List(s"${n.id}: every expect returns ${Example.show(v)}, so an implementation that always returns it would pass the examples; add an expect with another result")
          case _ => Nil
      },
      (params.filter(_.means.trim.isEmpty).map(_.name) ++ opaques.filter(_.means.trim.isEmpty).map(_.name))
        .map(n => s"$n: say what it means in the world"),
      opaques.map(_.name).filterNot((nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.opaques).++(definitions.flatMap(_.defines)).contains)
        .map(n => s"opaque type $n: the val name and the name given to Opaque differ"),
      implementations.map(_.contract).filterNot(c => nodes.exists(n => n.id == c && n.op.isDefined))
        .map(c => s"implementation of $c: not a contract (or an assumption on an operation) of this knowledge base"),
      (params.map(_.name) ++ opaques.map(_.name)).distinct.filter(Generate.reserved)
        .map(n => s"parameter or opaque type $n: the name is reserved in generated Lean"),
      ids.filter(i => names.contains(i) || params.exists(_.name == i) || opaques.exists(_.name == i))
        .map(i => s"node id $i clashes with a type, function or term of the same name"),
      (params.map(_.name) ++ opaques.map(_.name)).filter(names.contains).distinct.map(n => s"term $n clashes with a type or function of the same name"),
      nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement"),
      nodes.flatMap(_.lifted).flatMap(_.paramRefs).map(_._1).distinct.filterNot(n => params.exists(_.name == n))
        .map(n => s"parameter $n: the val name and the name given to Param differ"),
      (nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.lean).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten

  /** Runs the command line on a workspace (see `Cli`). */
  def cli(args: Seq[String], root: String = ".", kernelPath: String = "../../../lean"): Int =
    Cli.run(this, Cli.workspace(root, kernelPath), args)
