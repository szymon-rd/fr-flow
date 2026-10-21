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

/** A node of the knowledge base. It specifies a model of type `M`: a Scala value
  * (usually a function) describing what the system does at this level.
  *
  *   - root: `spec` says which models are acceptable. It is the root theorem.
  *   - refine: a more concrete model, `abs` to the parent's model, and `spec`;
  *     proven: `spec m → parent.spec (abs m)`.
  *   - instantiate: fixes opaque types and parameters of the parent.
  *   - contract: `post(a, b, result)` for every call of an implementation;
  *     proven to imply the parent's spec. Implementations are plain Scala,
  *     attached with `enforce`.
  *
  * Every node gets a Lean theorem `root`: the root's spec holds for its models.
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
    val cases: List[Example] = Nil
):
  def lifted: List[Lifted[?]] = spec.toList ++ abs.toList ++ post.toList ++ substs.flatMap(_.term)

  /** A more concrete model. `why` is the reason for this step, including why `abs` maps it faithfully. */
  inline def refine[M2](id: String, statement: String, why: String)(inline abs: M2 => M, inline spec: M2 => Boolean): Node[M2] =
    Node(id, statement, why, NodeKind.Refine, Some(this), Some(Lifted(spec)), Some(Lifted(abs)), None, Nil)

  /** Fixes opaque types and parameters. `why` says why these are the right meanings in the world. */
  def instantiate[M2](id: String, statement: String, why: String)(substs: Subst*): Node[M2] =
    Node(id, statement, why, NodeKind.Instantiate, Some(this), None, None, None, substs.toList)

  /** A contract for implementations with two inputs: `post(a, b, result)` holds for every call. */
  inline def contract[A, B, R](id: String, statement: String, why: String)(inline post: (A, B, R) => Boolean)(using
      M =:= ((A, B) => R)
  ): Node[(A, B) => R] =
    Node(id, statement, why, NodeKind.Contract, Some(this), None, None, Some(Lifted(post)), Nil)

  private[frflow] def withExamples(es: List[Example]): Node[M] =
    Node(id, statement, why, kind, parent, spec, abs, post, substs, cases ++ es)

  override def toString: String = id

object Node:
  /** A root: the formal statement of (one concern of) the project's idea. `why` says why it captures the idea. */
  inline def root[M](id: String, statement: String, why: String)(inline spec: M => Boolean): Node[M] =
    Node(id, statement, why, NodeKind.Root, None, Some(Lifted(spec)), None, None, Nil)

/** A concrete case of a contract, under given parameter values: the call `(a, b)`
  * with `result`. An `expect`ed case must be accepted by the contract and returned by
  * the implementation; a `reject`ed one must be refused by the contract.
  */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], a: Any, b: Any, result: Any, expected: Boolean):
  def call: String = s"(${Example.show(a)}, ${Example.show(b)}) ⇒ ${Example.show(result)}"
  def describe: String = s"${if expected then "expect" else "reject"} $call  given ${givenSource.mkString(", ")}  — $note"

object Example:
  def show(v: Any): String = v match
    case s: String => "\"" + s + "\""
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
final case class ExampleResult(example: Example, contract: String, implementation: Option[String])

/** Raised by an enforced implementation whose result breaks its contract. */
final class ContractViolation(node: String, detail: String) extends RuntimeException(s"$node: $detail")

extension [A, B, R](n: Node[(A, B) => R])
  /** Attaches a plain Scala implementation to a contract. Every call checks the
    * contract on its result and fails closed: a result that breaks it is never
    * returned.
    */
  def enforce(impl: (A, B) => R)(bindings: Binding*): (A, B) => R =
    require(n.kind == NodeKind.Contract, s"${n.id} is not a contract")
    val post = n.post.get.value.asInstanceOf[(A, B, R) => Boolean]
    (a, b) =>
      val r = impl(a, b)
      if Bindings.within(bindings)(post(a, b, r)) then r
      else throw ContractViolation(n.id, s"result $r for ($a, $b) breaks the contract")

  /** Concrete cases of the contract, under the given parameter values. They show what
    * the contract means, and they fail when it is vacuous, too weak, or when the
    * implementation does not do what was decided.
    */
  inline def examples(inline bindings: Binding*)(cases: Case[A, B, R]*): Node[(A, B) => R] =
    n.withExamples(cases.toList.map(c => Example(c.note, bindings.toList, Lifted.sources(bindings*), c.a, c.b, c.result, c.expected)))

  /** Each example, checked against the contract and, if given, against an implementation
    * built under the example's parameter values.
    */
  def checkExamples(impl: Option[() => (A, B) => R]): List[ExampleResult] =
    val post = n.post.get.value.asInstanceOf[(A, B, R) => Boolean]
    def attempt(f: => String) = try f catch case e: Exception => s"error: ${e.getMessage}"
    n.cases.map { e =>
      val (a, b, r) = (e.a.asInstanceOf[A], e.b.asInstanceOf[B], e.result.asInstanceOf[R])
      Bindings.within(e.bindings) {
        val c = attempt {
          val ok = post(a, b, r)
          if ok == e.expected then "ok" else if e.expected then "the contract refuses it" else "the contract accepts it"
        }
        val i = impl.map(mk => attempt {
          val got = mk()(a, b)
          if e.expected == (got == r) then "ok" else s"returned ${Example.show(got)}"
        })
        ExampleResult(e, c, i)
      }
    }

/** A plain Scala implementation registered for a contract, so its examples run against it. */
final case class Implementation(contract: String, run: () => List[ExampleResult])

/** A knowledge base: the developer's idea (a Markdown file) and the nodes derived from it.
  * `name` is the Lean namespace.
  */
final class KnowledgeBase(val name: String, val idea: String, val implementations: List[Implementation] = Nil)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList

  def node(id: String): Option[Node[?]] = nodes.find(_.id == id)
  def roots: List[Node[?]] = nodes.filter(_.kind == NodeKind.Root)
  def rootOf(n: Node[?]): Node[?] = path(n).head

  /** Registers the implementation of a contract. `impl` is built under each example's
    * parameter values, so it can read them (`grants.value`).
    */
  def implement[A, B, R](contract: Node[(A, B) => R])(impl: => (A, B) => R): KnowledgeBase =
    KnowledgeBase(name, idea, implementations :+ Implementation(contract.id, () => contract.checkExamples(Some(() => impl))))(nodes*)

  /** The results of a node's examples, against the implementation when one is registered. */
  def exampleResults(n: Node[?]): List[ExampleResult] =
    if n.cases.isEmpty then Nil
    else implementations.find(_.contract == n.id).fold(n.asInstanceOf[Node[(Any, Any) => Any]].checkExamples(None))(_.run())
  def children(n: Node[?]): List[Node[?]] = nodes.filter(_.parent.contains(n))
  def path(n: Node[?]): List[Node[?]] = n.parent.fold(List(n))(p => path(p) :+ n)
  def ordered: List[Node[?]] = nodes.sortBy(path(_).size)

  private def allLifted: List[Lifted[?]] =
    nodes.flatMap(_.lifted)

  /** Defined functions used anywhere, dependencies first. */
  def defs: List[Def[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
    val visiting = scala.collection.mutable.Set.empty[String]
    def visit(d: Def[?]): Unit =
      if !out.contains(d.name) && !visiting(d.name) then
        visiting += d.name
        d.lifted.defs.foreach(visit)
        visiting -= d.name
        out(d.name) = d
    nodes.flatMap(_.lifted).flatMap(_.defs).foreach(visit)
    out.values.toList

  /** Parameters used anywhere. */
  def params: List[Param[?]] =
    (nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.paramObjects).groupBy(_.name).values.map(_.head).toList.sortBy(_.name)

  /** Domain types used anywhere, dependencies first. */
  def types: List[TypeDecl] =
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
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      if roots.isEmpty then List("a root node is required") else Nil,
      nodes.filter(_.why.trim.isEmpty).map(n => s"${n.id}: say why (the reason for this node)"),
      nodes.filter(n => n.cases.nonEmpty && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts have examples"),
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
