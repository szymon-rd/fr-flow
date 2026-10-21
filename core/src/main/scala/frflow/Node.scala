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
    val kind: NodeKind,
    val parent: Option[Node[?]],
    val spec: Option[Lifted[?]],
    val abs: Option[Lifted[?]],
    val post: Option[Lifted[?]],
    val substs: List[Subst]
):
  def lifted: List[Lifted[?]] = spec.toList ++ abs.toList ++ post.toList ++ substs.flatMap(_.term)

  /** A more concrete model. */
  inline def refine[M2](id: String, statement: String)(inline abs: M2 => M, inline spec: M2 => Boolean): Node[M2] =
    Node(id, statement, NodeKind.Refine, Some(this), Some(Lifted(spec)), Some(Lifted(abs)), None, Nil)

  /** Fixes opaque types and parameters. `M2` is the model type after substitution; Lean checks it. */
  def instantiate[M2](id: String, statement: String)(substs: Subst*): Node[M2] =
    Node(id, statement, NodeKind.Instantiate, Some(this), None, None, None, substs.toList)

  /** A contract for implementations with two inputs: `post(a, b, result)` holds for every call. */
  inline def contract[A, B, R](id: String, statement: String)(inline post: (A, B, R) => Boolean)(using
      M =:= ((A, B) => R)
  ): Node[(A, B) => R] =
    Node(id, statement, NodeKind.Contract, Some(this), None, None, Some(Lifted(post)), Nil)

  override def toString: String = id

object Node:
  /** The root: the formal statement of the project's idea. */
  inline def root[M](id: String, statement: String)(inline spec: M => Boolean): Node[M] =
    Node(id, statement, NodeKind.Root, None, Some(Lifted(spec)), None, None, Nil)

/** Raised by an enforced implementation whose result breaks its contract. */
final class ContractViolation(node: String, detail: String) extends RuntimeException(s"$node: $detail")

extension [A, B, R](n: Node[(A, B) => R])
  /** Attaches a plain Scala implementation to a contract. Every call checks the
    * contract on its result and fails closed: a result that breaks it is never
    * returned. The root theorem therefore holds for every result the system returns.
    */
  def enforce(impl: (A, B) => R)(bindings: Binding*): (A, B) => R =
    require(n.kind == NodeKind.Contract, s"${n.id} is not a contract")
    val post = n.post.get.value.asInstanceOf[(A, B, R) => Boolean]
    (a, b) =>
      val r = impl(a, b)
      if Bindings.within(bindings)(post(a, b, r)) then r
      else throw ContractViolation(n.id, s"result $r for ($a, $b) breaks the contract")

/** A knowledge base: the developer's idea (a Markdown file) and the nodes derived from it.
  * `name` is the Lean namespace.
  */
final class KnowledgeBase(val name: String, val idea: String)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList

  def node(id: String): Option[Node[?]] = nodes.find(_.id == id)
  def root: Node[?] = nodes.find(_.kind == NodeKind.Root).getOrElse(throw IllegalStateException("no root node"))
  def children(n: Node[?]): List[Node[?]] = nodes.filter(_.parent.contains(n))
  def path(n: Node[?]): List[Node[?]] = n.parent.fold(List(n))(p => path(p) :+ n)
  def ordered: List[Node[?]] = nodes.sortBy(path(_).size)

  private def allLifted: List[Lifted[?]] =
    nodes.flatMap(_.lifted) ++ params.flatMap(_.assumption)

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
    (nodes.flatMap(_.lifted) ++ nodes.flatMap(_.lifted).flatMap(_.paramObjects).flatMap(_.assumption)).flatMap(_.defs).foreach(visit)
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
      if nodes.count(_.kind == NodeKind.Root) != 1 then List("exactly one root node is required") else Nil,
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
