package frflow

/** How a node relates to its parent. */
enum NodeKind:
  /** The formal statement of the idea. */
  case Root
  /** A more concrete model, with an abstraction to the parent's model; proven. */
  case Refine
  /** The parent with its opaque types and parameters fixed; nothing to prove. */
  case Instantiate
  /** A per-call contract for implementations; proven to imply the parent. */
  case Contract
  /** A design decision with no formal model (an architecture choice, a convention); it
    * governs source files, and a change to them is noticed. Nothing to prove.
    */
  case Design
  /** A cross-cutting rule (such as "no cross-tenant read"), stated once as a formal rule over pairs
    * (such as a reader and a record). Every contract in its scope keeps it (`keeps`, naming which
    * pairs a call exposes, proven from its post) or says why it does not apply (`exempt`). It has
    * no parent.
    */
  case Invariant

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

/** A node of the knowledge base. It specifies a model of type `M`: a Scala value
  * (usually a function) describing what the system does at this level.
  *
  *   - root: `spec` says which models are acceptable. It is the root theorem.
  *   - refine: a more concrete model, `abs` to the parent's model, and `spec`;
  *     proven: `spec m → parent.spec (abs m)`.
  *   - instantiate: fixes opaque types and parameters of the parent.
  *   - contract: `post(a, b, result)` for every call of an implementation;
  *     proven to imply the parent's spec. Implementations are `define`s Lean proves
  *     (`KnowledgeBase.implementProven`), or plain Scala checked by running (`implement`).
  *
  * Every node gets a Lean theorem `root`: the root's spec holds for its models. A node can opt out
  * with `formal = false`: its model stays Scala (a contract's post still runs its examples
  * and `service`), nothing is translated to Lean, and its link is decided by reading. Everything
  * below it is out of Lean too, since there is nothing formal above it to prove against.
  */
final class Node[M] @scala.annotation.publicInBinary private[frflow] (
    val id: String,
    val statement: String,
    val why: String,
    val kind: NodeKind,
    val parent: Option[Node[?]],
    val spec: Option[Lifted[?]],
    val abs: Option[Lifted[?]],
    val post: Option[Lifted[?]],
    val substs: List[Subst],
    val cases: List[Example] = Nil,
    val governs: List[String] = Nil,
    val declaredFormal: Boolean = true,
    val kept: List[Keep] = Nil,
    val scope: List[Node[?]] = Nil,
    val ideaSection: String = "",
    val file: String = "",
    val expected: List[(String, Lifted[?])] = Nil,
    val relied: List[(() => Node[?], String, Option[Reliance])] = Nil,
    val at: Int = -1,
    val safety: String = "",
    val local: Option[Lifted[?]] = None,
    val owner: String = ""
):
  /** The nodes this one relies on besides its parent (see `relies`), with what it relies on. */
  def reliesOn: List[(Node[?], String)] = relied.map((f, why, _) => (f(), why))

  /** What it relies on that is stated as a property of the parameters, checked wherever it runs. */
  def reliedProperties: List[(Node[?], String, Reliance)] = relied.collect { case (f, why, Some(p)) => (f(), why, p) }

  /** This node relies on what another node says (often of another concern: the read side on what
    * every write keeps); `why` says what. A change to that node's meaning puts this one up for review,
    * as a change above it does, and accepting such a change lists this one among the decisions it may
    * affect. The other node may be declared later.
    */
  def relies(on: => Node[?], why: String): Node[M] = copy(relied = relied :+ (() => on, why, None))

  /** Relies on `on` for a guarantee about the states `on`'s concern reaches, and on this node seeing
    * such a state (`sees`, built from its parameters). CRM's reads: `(s: CrmStore) => consistentStore(s)`,
    * seeing `() => CrmStore(store.value, shares.value)`. Lean proves the guarantee of every state `on`'s
    * concern reaches, from `on`'s root theorem (`rely_<on>`); every example and every call through
    * `service` checks it of the state this node sees. What is trusted is one named thing: that the state
    * it sees is one `on`'s concern reached (the wiring that binds its parameters).
    */
  inline def relies[S](on: => Node[?], why: String, inline guarantee: S => Boolean)(inline sees: () => S): Node[M] =
    copy(relied = relied :+ (() => on, why, Some(Reliance(Lifted(guarantee), Lifted(sees)))))

  /** Whether Lean checks this node: it did not opt out, and neither did anything above it. */
  def formal: Boolean = declaredFormal && parent.forall(_.formal)

  /** The parts translated to Lean; none when the node is out of Lean. */
  def lifted: List[Lifted[?]] = if !formal then Nil else referenced

  /** The node's lambdas, translated or not: what it refers to (definitions, parameters, opaque types)
    * is known either way, so a change to them reaches it.
    */
  def referenced: List[Lifted[?]] = spec.toList ++ abs.toList ++ post.toList ++ local.toList ++ substs.flatMap(_.term) ++ kept.flatMap(_.view) ++
    expected.map(_._2) ++ relied.flatMap(_._3).flatMap(r => List(r.guarantee, r.sees))

  /** A consequence the developer expects of every model of this node, stated as a check of their
    * understanding (Lean proves it from the node's spec): "Acme never sees Globex's unshared contact".
    */
  inline def expects(statement: String)(inline consequence: M => Boolean): Node[M] =
    copy(expected = expected :+ (statement -> Lifted.of(true, consequence)))

  /** A more concrete model. `why` is the reason for this step, including why `abs` maps it faithfully. */
  inline def refine[M2](id: String, statement: String, why: String, inline formal: Boolean = true)(
      inline abs: M2 => M, inline spec: M2 => Boolean): Node[M2] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[M2] =
      Node(id, statement, why, NodeKind.Refine, Some(this), Some(Lifted.of(formal, spec)), Some(Lifted.of(formal, abs)), None, Nil,
        declaredFormal = formal, file = Lifted.here, at = Lifted.at)
    node()

  /** Fixes opaque types and parameters. `why` says why these are the right meanings in the world. */
  inline def instantiate[M2](id: String, statement: String, why: String, formal: Boolean = true)(substs: Subst*): Node[M2] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[M2] =
      Node(id, statement, why, NodeKind.Instantiate, Some(this), None, None, None, substs.toList, declaredFormal = formal, file = Lifted.here, at = Lifted.at)
    node()

  /** A contract for implementations with two inputs: `post(a, b, result)` holds for every call. */
  inline def contract[A, B, R](id: String, statement: String, why: String, inline formal: Boolean = true)(
      inline post: (A, B, R) => Boolean)(using M =:= ((A, B) => R)): Node[(A, B) => R] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, Some(this), None, None, Some(Lifted.of(formal, post)), Nil, declaredFormal = formal, file = Lifted.here, at = Lifted.at)
    node()

  private def copy(cases: List[Example] = cases, governs: List[String] = governs, kept: List[Keep] = kept,
      expected: List[(String, Lifted[?])] = expected, relied: List[(() => Node[?], String, Option[Reliance])] = relied,
      local: Option[Lifted[?]] = local): Node[M] =
    Node(id, statement, why, kind, parent, spec, abs, post, substs, cases, governs, declaredFormal, kept, scope, ideaSection, file, expected,
      relied, at, safety, local, owner)

  /** A contract with a signature of its own: `abs` says what an implementation is as the parent's
    * model (a new read path below an existing instantiation, say). Proven: `spec f → parent.spec (abs f)`.
    */
  inline def contractVia[A, B, R](id: String, statement: String, why: String, inline formal: Boolean = true)(
      inline abs: ((A, B) => R) => M)(inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, Some(this), None, Some(Lifted.of(formal, abs)), Some(Lifted.of(formal, post)), Nil,
        declaredFormal = formal, file = Lifted.here, at = Lifted.at)
    node()

  private[frflow] def withExamples(es: List[Example]): Node[M] =
    copy(cases = cases ++ es)

  private[frflow] def withKeeps(ks: List[Keep]): Node[M] =
    copy(kept = ks)

  private[frflow] def withLocal(l: Lifted[?]): Node[M] = copy(local = Some(l))

  /** A design decision below this node, with no formal model: an architecture choice or a
    * convention. `governs` are the source files it is about (relative to the project), so a
    * change to them is noticed.
    */
  inline def design(id: String, statement: String, why: String)(governs: String*): Node[Unit] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, Some(this), None, None, None, Nil, Nil, governs.toList, file = Lifted.here, at = Lifted.at)
    node()

  /** The invariant does not apply to this contract or design decision, for the reason given (part of
    * what the node says, so the developer reads it).
    */
  def exempt(invariant: Node[?], because: String): Node[M] =
    require(invariant != null, s"$id is exempt from an invariant declared after it: declare the invariant first")
    withKeeps(kept :+ Keep(invariant, None, because))

  override def toString: String = id

object Node:
  /** A port: a contract for what lies outside the proven core (a database, an HTTP client, a clock),
    * with no parent: its post is what the outside is trusted to do, decided like any node. Code that
    * calls it (`port.caller`) is proven from that promise; its adapter is plain code, checked at run
    * time (give the port a cheap `checkedBy`).
    */
  inline def port[A, B, R](id: String, statement: String, why: String)(inline post: (A, B, R) => Boolean): Node[(A, B) => R] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[(A, B) => R] =
      Node(id, statement, why, NodeKind.Contract, None, None, None, Some(Lifted.of(true, post)), Nil, file = Lifted.here, at = Lifted.at)
    node()

  /** A root: the formal statement of (one concern of) the project's idea. `why` says why it captures
    * the idea. `idea` names the `## ` section of IDEA.md it is decided against (the text before the
    * first section counts for every root); without it, the root is decided against the whole idea.
    */
  /** `safety`: why the root only says what must not happen, when doing nothing meets it (a root that
    * says what users can do, a capability, needs none). Without it, such a root is unproven.
    * `owner`: the developer who decides this concern (every node below it); none, anyone.
    */
  inline def root[M](id: String, statement: String, why: String, inline formal: Boolean = true, idea: String = "", safety: String = "",
      owner: String = "")(
      inline spec: M => Boolean): Node[M] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[M] =
      Node(id, statement, why, NodeKind.Root, None, Some(Lifted.of(formal, spec)), None, None, Nil, declaredFormal = formal, ideaSection = idea,
        file = Lifted.here, at = Lifted.at, safety = safety, owner = owner)
    node()

  /** A cross-cutting invariant: `rule(a, b)` holds for every pair a call exposes (such as a reader
    * and a record returned to them), stated once. Every contract below the `scope` nodes (every
    * contract of the knowledge base when none are given) keeps it (`keeps`) or is `exempt`.
    */
  inline def invariant[A, B](id: String, statement: String, why: String, scope: List[Node[?]] = Nil, inline formal: Boolean = true)(
      inline rule: (A, B) => Boolean): Node[(A, B) => Boolean] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Invariant, None, Some(Lifted.of(formal, rule)), None, None, Nil, declaredFormal = formal, scope = scope,
        file = Lifted.here, at = Lifted.at)
    node()

  /** A design decision on its own, with no formal model (see `Node.design`). */
  inline def design(id: String, statement: String, why: String)(governs: String*): Node[Unit] =
    // Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, None, None, None, None, Nil, Nil, governs.toList, file = Lifted.here, at = Lifted.at)
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
  /** A parameter standing for any implementation of this contract, for code that calls it: Lean proves
    * the calling code assuming only what this contract promises (its `post`), and the caller rests on
    * this contract. Bind it at run time to the contract's `service`.
    */
  def caller(name: String): Param[(A, B) => R] =
    Param(name, s"any implementation of ${n.id}: what it returns meets ${n.id}'s contract", Some(() => n))

  /** What `service` checks on every call instead of the whole post: a check of the result alone (each
    * returned row matches the query, say), cheap where the post reads all the data. Lean proves the
    * post implies it, so it refuses nothing the contract allows; what it leaves out (that nothing is
    * missing) rests on the proofs, and on the port's promise.
    */
  inline def checkedBy(inline check: (A, B, R) => Boolean): Node[(A, B) => R] = n.withLocal(Lifted.of(true, check))

  /** A plain Scala implementation with every call checked against the contract: a result that
    * breaks it is never returned. Used by `KnowledgeBase.service`, which is how code is attached.
    */
  private[frflow] def enforce(impl: (A, B) => R, assumes: List[Assumption] = Nil)(bindings: Binding*): (A, B) => R =
    require(n.kind == NodeKind.Contract, s"${n.id} is not a contract")
    // The cheap check when the contract gives one (Lean proves the post implies it), else the post.
    val check = n.local.getOrElse(n.post.get).value.asInstanceOf[(A, B, R) => Boolean]
    val what = if n.local.isDefined then "its check" else "the contract"
    // What each relied-on guarantee was last found to hold of: checked again when a value it reads changes.
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
            if !x.holds() then throw ContractViolation(n.id, s"the values it runs with break what ${x.what}")
            held.put(x.what, vs)
        }
        r
      }

  /** This contract keeps an invariant: `view(a, b, result)` lists the pairs the call exposes to it
    * (such as `result.map(r => (reader, r))`), and the invariant's rule holds for each. Lean proves
    * it from the post, and that the view is not empty-handed (a view whose pairs always meet the
    * rule, whatever the call returns, keeps nothing); it is also checked on the examples and at run
    * time.
    */
  inline def keeps[X, Y](invariant: Node[(X, Y) => Boolean], inline formal: Boolean = true, reader: Int = -1)(
      inline view: (A, B, R) => List[(X, Y)]): Node[(A, B) => R] =
    require(invariant != null, s"${n.id} keeps an invariant declared after it: declare the invariant first")
    n.withKeeps(n.kept :+ Keep(invariant, Some(Lifted.of(formal, view)), reader = reader))

  /** The first invariant a call's result breaks, if any. */
  def broken(a: A, b: B, r: R): Option[String] =
    n.kept.find { k =>
      k.view.exists { v =>
        val rule = k.invariant.spec.get.value.asInstanceOf[(Any, Any) => Boolean]
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
          val broken = assumes.find(!_.holds())
          if broken.isDefined then s"the values it gives break what ${broken.get.what}"
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

/** What a node relies on another concern for: a guarantee about the states that concern reaches, and the
  * state this node sees (built from its parameters).
  */
/** A guarantee relied on, checked where code runs: what it is, the parameters it reads, whether it holds now. */
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

final case class Reliance(guarantee: Lifted[?], sees: Lifted[?]):
  /** The guarantee, of the state seen now (under the parameters bound). */
  def holds: Boolean = guarantee.value.asInstanceOf[Any => Boolean](sees.value.asInstanceOf[() => Any]())

/** An implementation registered for a contract: its examples run against it, production runs it
  * through `KnowledgeBase.service`, and a change to its source files is noticed. `wiring` is the
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


/** A knowledge base: the developer's idea (a Markdown file) and the nodes derived from it.
  * `name` is the Lean namespace.
  */
/** A node another knowledge base decides: its name, the project directory (where its ledger and keys
  * are), and its idea file.
  */
final case class Imported(kb: String, root: String, idea: String)

final class KnowledgeBase(val name: String, val idea: String, val implementations: List[Implementation] = Nil,
    val imports: Map[String, Imported] = Map.empty)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList

  /** Contracts of another knowledge base this one's code calls (`caller`) or relies on (`relies`): decided
    * and checked there (`root`, that project's directory: its ledger and keys hold their decisions). They
    * come with the nodes above them, the invariants they keep and their code, for Lean and for running;
    * here they are read: a change to one there reviews what rests on it here.
    */
  def uses(other: KnowledgeBase, root: String)(contracts: Node[?]*): KnowledgeBase =
    val brought = contracts.toList.flatMap(other.path).distinct
    val withKept = (brought ++ brought.flatMap(_.kept.map(_.invariant))).distinct.filterNot(n => nodes.exists(_ eq n))
    KnowledgeBase(name, idea, implementations ++ other.implementations.filter(i => brought.exists(_.id == i.contract)),
      imports ++ withKept.map(n => n.id -> Imported(other.name, root, other.idea)))((nodes ++ withKept)*)

  def node(id: String): Option[Node[?]] = nodes.find(_.id == id)
  def roots: List[Node[?]] = nodes.filter(_.kind == NodeKind.Root)
  def rootOf(n: Node[?]): Node[?] = path(n).head

  /** Registers the implementation of a contract. `impl` is built under the parameter values of
    * each example and of each production call, so it can read them (`grants.value`).
    */
  inline def implement[A, B, R](contract: Node[(A, B) => R])(inline impl: (A, B) => R): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => impl, Lifted.sourceFiles(impl), Lifted.sources(impl).mkString))

  /** Registers an implementation written as a `define`, in the Scala Lean translates: besides its
    * examples and the run-time check, Lean proves that every result it returns meets the contract
    * (and the invariants the contract keeps), so the proven chain reaches the code itself.
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

  /** The running system: the registered implementation of `contract`, reading the given parameter
    * values, with every result checked against the contract (see `enforce`).
    */
  def service[A, B, R](contract: Node[(A, B) => R])(bindings: Binding*): (A, B) => R =
    val i = implementation(contract).getOrElse(throw IllegalStateException(s"no implementation of ${contract.id}"))
    val f = i.factory.asInstanceOf[() => (A, B) => R]
    // Fail when wired, not on the first call: every parameter the contract or its examples read
    // must be bound (a contract that starts reading a new parameter breaks old wiring here).
    val needed = (contract.post.toList.flatMap(_.paramObjects) ++ contract.cases.flatMap(_.bindings.map(_.param))).map(_.name).distinct
    val missing = needed.filterNot(bindings.map(_.param.name).contains)
    if missing.nonEmpty then
      throw IllegalStateException(s"${contract.id}: bind ${missing.mkString(", ")} (the contract reads them)")
    // A `caller` the code reads runs the service of its contract, under the same values.
    val calls = callers { (c, _) =>
      lazy val s = service(c.asInstanceOf[Node[(Any, Any) => Any]])(bindings*)
      val g = (x: Any, y: Any) => s(x, y)
      () => g
    }
    // The guarantees relied on hold of the values it starts with; later, whenever a call reads them anew.
    val assumes = assumptionsOf(contract)
    Bindings.within(bindings)(assumes.find(!_.holds())).foreach(x => throw ContractViolation(contract.id, s"the values it starts with break what ${x.what}"))
    contract.enforce((a, b) => f()(a, b), assumes)((calls ++ bindings)*)

  /** Each `caller` bound to its contract's registered code, as examples run it. */
  def callerCode: List[Binding] = callers((_, i) => () => i.factory())

  /** Each `caller` parameter of the model whose contract has registered code, bound by `bind`. */
  private def callers(bind: (Node[?], Implementation) => () => Any): List[Binding] =
    params.flatMap(p => p.implementing.map(_()).flatMap(c => implementation(c).map(i => Binding(p, bind(c, i)))))

  /** The guarantees the nodes on a contract's path rely on (see `relies`), to check where it runs. */
  def assumptionsOf(n: Node[?]): List[Assumption] =
    path(n).flatMap(x => x.reliedProperties.map((o, why, r) => Assumption(s"${x.id} relies on ${o.id} for (${why}): `${r.guarantee.source}` of `${r.sees.source}`",
      (r.sees.paramObjects ++ r.guarantee.paramObjects).map(_.name).toSet, () => r.holds)))

  /** The results of a node's examples, against the implementation when one is registered. */
  def exampleResults(n: Node[?]): List[ExampleResult] =
    // An example need not bind a `caller`: it runs its contract's registered code, under the example's values.
    if n.cases.isEmpty then Nil
    else Bindings.within(callerCode) { n.asInstanceOf[Node[(Any, Any) => Any]].checkExamples(implementation(n).map(_.factory.asInstanceOf[() => (Any, Any) => Any]), assumptionsOf(n)) ++
      generated(n) }

  /** The contract holds for every call, not only the examples: the implementation also runs on
    * every combination of the examples' inputs, under each example's parameter values. Calls whose
    * result breaks the contract are listed as failing.
    */
  def generated(n: Node[?]): List[ExampleResult] =
    implementation(n).filter(_ => n.kind == NodeKind.Contract && n.cases.nonEmpty).toList.flatMap { i =>
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

  /** What a contract does not promise, found mechanically: inputs its `post` never looks at, and
    * whether an empty result (`None`, `Nil`) satisfies it for every example input. Shown next to
    * the decision, so nobody believes a contract says more than it does.
    */
  def limits(n: Node[?]): List[String] =
    assumptions(n).map(c => s"it assumes about the world, whatever the model does: `$c`") ++ unread(n) ++
    n.abs.filter(a => n.formal && """\bif\b|\bmatch\b|List\.filter""".r.findFirstIn(a.body).isDefined)
      .map(a => s"its abs chooses by a condition what reaches the parent: read it, since what it leaves out is not proven: `${a.source}`").toList ++ (
    if n.kind != NodeKind.Contract then Nil
    else
      val post = n.post.get
      val unused = if !n.formal then Nil else post.params.init.map(_._1).filterNot(p => (s"(?<![\\w'])${java.util.regex.Pattern.quote(p)}(?![\\w'])").r.findFirstIn(post.body).isDefined)
      val f = post.value.asInstanceOf[(Any, Any, Any) => Boolean]
      val empties = n.cases.flatMap { e =>
        val empty = e.result match
          case _: Option[?] => Some(None)
          case _: List[?]   => Some(Nil)
          case _            => None
        empty.map(v => try Bindings.within(e.bindings)(f(e.a, e.b, v)) catch case _: Exception => false)
      }
      unused.map(p => s"the result may not depend on `$p`: the contract never looks at it") ++
        (if empties.nonEmpty && empties.forall(identity) then
          List("an empty result (None or Nil) always satisfies it: it never requires the system to return anything") else Nil))

  /** Parameters a contract's ancestors use (and do not substitute away) that its post never reads:
    * a requirement above that the contract may have dropped.
    */
  def unread(n: Node[?]): List[String] =
    if n.kind != NodeKind.Contract then Nil
    else
      val above = path(n).dropRight(1)
      val substituted = above.flatMap(_.substs).map(_.name).toSet
      val reads = n.referenced.flatMap(_.paramObjects).map(_.name).toSet ++
        n.referenced.flatMap(_.defs).flatMap(d => d.lifted.paramObjects.map(_.name))
      above.reverse.flatMap(a => a.referenced.flatMap(_.paramObjects).map(p => p.name -> a.id)).distinctBy(_._1)
        .filterNot((p, _) => reads(p) || substituted(p))
        .map((p, a) => s"it never reads `$p`, which $a uses")

  /** Top-level conditions of a spec (or post) that never mention the model (or the call): they
    * constrain the world, not the system, and can do a proof's work.
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
    val l = if !n.formal then None else if n.kind == NodeKind.Contract then n.post else n.spec
    l.toList.flatMap { f =>
      val names = f.params.map(_._1)
      if names.isEmpty then Nil
      else split(f.body).filterNot(c => names.exists(b => s"(?<![\\w'.])${java.util.regex.Pattern.quote(b)}(?![\\w'])".r.findFirstIn(c).isDefined))
    }

  /** The opaque types used anywhere. */
  def opaques: List[Opaque] =
    (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.opaqueObjects).groupBy(_.name).values.map(_.head).toList.sortBy(_.name)
  def children(n: Node[?]): List[Node[?]] = nodes.filter(_.parent.contains(n))

  /** The contracts and design decisions an invariant applies to, below its scope (or anywhere): the
    * contracts whose result can hold what the rule is about, and the design decisions below a contract
    * that keeps it (they govern code no proof covers on that path, and say why it does not break it).
    */
  def inScope(i: Node[?]): List[Node[?]] =
    // What the rule is about (the second of its pairs, such as a record), as a Lean type.
    val about = i.spec.flatMap(_.params.lift(1)).map(_._2)
    // A type holds it if it names it, or names a type that holds it (a store of records).
    val uses = types.map(t => t.name -> t.uses).toMap
    def holds(t: String, seen: Set[String] = Set.empty): Boolean =
      val names = """[A-Za-z_][\w.]*""".r.findAllIn(t).toList
      about.forall(a => names.contains(a) || names.filterNot(seen).exists(n => uses.get(n).exists(u => holds(u.mkString(" "), seen + n))))
    def mentions(t: String) = holds(t)
    def returnsIt(c: Node[?]) = c.post.forall(p => p.params.isEmpty || mentions(p.params.last._2))
    def keeper(c: Node[?]) = c.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    // Another knowledge base's invariant is kept by its own contracts, not by this one's.
    nodes.filter(c => imports.contains(i.id) == imports.contains(c.id)).filter { c =>
      (i.scope.isEmpty || path(c).exists(a => i.scope.exists(_ eq a))) && (c.kind match
        case NodeKind.Contract => returnsIt(c)
        // A design decision governs code no proof covers: it is in scope below a contract that keeps
        // the rule, is exempt from it or returns what it is about (an exemption of the contract is
        // not one of the code hung below it), and with no contract above it at all.
        case NodeKind.Design   =>
          val contracts = path(c).filter(_.kind == NodeKind.Contract)
          contracts.isEmpty || contracts.exists(a => keeper(a) || a.kept.exists(_.invariant eq i) || returnsIt(a))
        case _                 => false)
    }
  def path(n: Node[?]): List[Node[?]] = n.parent.fold(List(n))(p => path(p) :+ n)
  def ordered: List[Node[?]] = nodes.sortBy(path(_).size)

  private def allLifted: List[Lifted[?]] =
    nodes.flatMap(_.lifted)

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

  /** Parameters used anywhere. */
  lazy val params: List[Param[?]] =
    (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.paramObjects).groupBy(_.name).values.map(_.head).toList.sortBy(_.name)

  /** Domain types used anywhere, dependencies first. */
  lazy val types: List[TypeDecl] =
    val all = (allLifted ++ defs.map(_.lifted)).flatMap(_.types) ++ nodes.flatMap(_.substs).flatMap(_.types)
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
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      // Another knowledge base's nodes are built on by calling or relying on them, not by refining them.
      nodes.filter(n => !imports.contains(n.id) && n.parent.exists(p => imports.contains(p.id)))
        .map(n => s"${n.id} is below ${n.parent.get.id}, which ${imports(n.parent.get.id).kb} decides: call it (caller) or rely on it (relies) instead"),
      // Code that calls its own contract would be proven assuming what it proves.
      nodes.filter(c => implementation(c).flatMap(_.proven).toList.flatMap(d => Def.closure(List(d))).flatMap(_.lifted.paramObjects)
        .exists(_.implementing.exists(f => f() eq c))).map(c => s"${c.id}: its implementation calls ${c.id} itself (through a caller): it cannot be proven from its own promise"),
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      ids.filter(_ == "Lemmas").map(_ => "node id Lemmas is reserved: lean/Proofs/<KB>/Lemmas.lean holds the lemmas the proofs share"),
      if roots.isEmpty then List("a root node is required") else Nil,
      nodes.filter(_.why.trim.isEmpty).map(n => s"${n.id}: say why (the reason for this node)"),
      nodes.filter(n => n.cases.nonEmpty && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts have examples"),
      nodes.flatMap(n => n.kept.map(_.invariant).filterNot(i => nodes.contains(i) && i.kind == NodeKind.Invariant)
        .map(i => s"${n.id} keeps ${i.id}, which is not an invariant of this knowledge base")),
      nodes.filter(n => n.kept.exists(_.view.nonEmpty) && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts keep invariants"),
      nodes.filter(n => n.kept.nonEmpty && n.kind != NodeKind.Contract && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: only contracts and design decisions are exempt from invariants"),
      nodes.flatMap(n => n.kept.groupBy(_.invariant.id).collect { case (i, ks) if ks.size > 1 => s"${n.id} names $i more than once" }),
      nodes.flatMap(n => n.kept.filter(k => k.view.isEmpty && Words.tooFew(k.exempt))
        .map(k => s"${n.id}: say in a few words why ${k.invariant.id} does not apply to it")),
      nodes.filter(_.kind == NodeKind.Invariant).flatMap(i => inScope(i).filterNot(_.kept.exists(_.invariant eq i))
        .map(c => if c.kind == NodeKind.Design then s"${c.id}: say why ${i.id} does not apply to the code it governs (.exempt): a design decision in its scope does"
          else s"${c.id}: keep ${i.id} (.keeps) or say why it does not apply (.exempt): every contract in its scope does one")),

      nodes.filter(i => i.kind == NodeKind.Invariant && !nodes.exists(_.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)))
        .map(i => s"${i.id}: no contract keeps this invariant"),
      // An opaque type something says exists of, fixed to a type that holds an Int or Long: Lean's
      // integers are unbounded, so what Lean finds may not exist in Scala.
      nodes.filter(_.kind == NodeKind.Instantiate).flatMap { n =>
        n.substs.filter(_.isType).filter(s => s.types.exists(t => """:\s*(Int|Long)\b""".r.findFirstIn(t.scala).isDefined)).flatMap { s =>
          val ex = s"∃ \\([^)]*: ${java.util.regex.Pattern.quote(s.name)}\\)".r
          path(n).flatMap(_.lifted).find(l => ex.findFirstIn(l.body).isDefined).map(_ =>
            s"${n.id}: ${s.name} := ${s.lean}, whose values hold an Int or Long, but something above says one exists: Lean's integers are unbounded, Scala's are not; use BigInt")
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
      nodes.flatMap(n => n.reliesOn.collect {
        case (null, _) => s"${n.id} relies on a node that is not initialized: refer to its val"
        case (o, _) if !nodes.contains(o) => s"${n.id} relies on ${o.id}, which is not in the knowledge base"
        case (o, why) if Words.tooFew(why) => s"${n.id}: say in a few words what it relies on in ${o.id}"
      }),
      // What a node rests on (its parent, what it relies on, the invariants it keeps) must not lead back to it.
      nodes.filter { n =>
        def on(x: Node[?]): List[Node[?]] = x.parent.toList ++ x.reliesOn.map(_._1).filter(_ != null) ++ x.kept.filter(_.view.nonEmpty).map(_.invariant)
        def reaches(from: List[Node[?]], seen: Set[Node[?]]): Boolean = from.exists(x => (x eq n) || (!seen(x) && reaches(on(x), seen + x)))
        reaches(n.reliesOn.map(_._1).filter(_ != null), Set.empty)
      }.map(n => s"${n.id} relies on a node that rests on it: what each rests on must not lead back to it"),
      nodes.filter(i => i.kind == NodeKind.Invariant).flatMap(i => i.scope.filterNot(nodes.contains).map(s => s"${i.id}: its scope ${s.id} is not in the knowledge base")),
      // Two different parameters (or opaque types) with one name would be one in Lean and at run time.
      (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.paramObjects).distinctBy(System.identityHashCode).groupBy(_.name)
        .collect { case (p, ps) if ps.size > 1 => s"two different parameters are named $p: ${ps.map(_.means).mkString("; ")}; rename one" }.toList.sorted,
      (nodes.flatMap(_.referenced) ++ defs.map(_.lifted)).flatMap(_.opaqueObjects).distinctBy(System.identityHashCode).groupBy(_.name)
        .collect { case (o, os) if os.size > 1 => s"two different opaque types are named $o; rename one" }.toList.sorted,
      nodes.filter(n => n.parent.exists(_.kind == NodeKind.Design) && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: a design decision has no model to specialize; only design decisions go below it"),

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
      opaques.map(_.name).filterNot((allLifted ++ defs.map(_.lifted)).flatMap(_.opaques).contains)
        .map(n => s"opaque type $n: the val name and the name given to Opaque differ"),
      implementations.map(_.contract).filterNot(c => nodes.exists(n => n.id == c && n.kind == NodeKind.Contract))
        .map(c => s"implementation of $c: not a contract of this knowledge base"),
      (params.map(_.name) ++ allLifted.flatMap(_.opaques)).distinct.filter(Generate.reserved)
        .map(n => s"parameter or opaque type $n: the name is reserved in generated Lean"),
      nodes.flatMap(n => n.parent.filterNot(nodes.contains).map(p => s"${n.id}: parent ${p.id} is not in the knowledge base")),
      ids.filter(names.contains).map(i => s"node id $i clashes with a type or function of the same name"),
      nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement"),
      allLifted.flatMap(_.paramRefs).map(_._1).distinct.filterNot(n => params.exists(_.name == n))
        .map(n => s"parameter $n: the val name and the name given to Param differ"),
      (allLifted ++ defs.map(_.lifted)).flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.lean).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten

  /** Runs the command line on a workspace (see `Cli`). */
  def cli(args: Seq[String], root: String = ".", kernelPath: String = "../../../lean"): Int =
    Cli.run(this, Cli.workspace(root, kernelPath), args)
