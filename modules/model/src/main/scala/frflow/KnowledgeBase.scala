package frflow

/** A knowledge base: the developer's idea (a Markdown file) and the nodes derived from it: one root
  * claim, refined by a DAG of parts, over a shared vocabulary. `name` is the Lean namespace.
  *
  * Immutable: its queries are functions of the nodes and the implementations, over indexes built once
  * (the lazy vals). Registering code (`implement`) gives a new knowledge base. Nodes are told apart by
  * identity (a `Node` has no structural equality), ids by name.
  */
final class KnowledgeBase(val name: String, val idea: String, val implementations: List[Implementation] = Nil)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList

  // ---------------------------------------------------------------------------
  // The DAG
  // ---------------------------------------------------------------------------

  private lazy val members: Set[Node[?]] = nodes.toSet
  /** Whether the node is one of this knowledge base's. */
  def has(n: Node[?]): Boolean = members(n)

  private lazy val byId: Map[String, Node[?]] = nodes.reverse.map(n => n.id -> n).toMap
  def node(id: String): Option[Node[?]] = byId.get(id)

  /** A node's parents in this knowledge base. */
  def parentsOf(n: Node[?]): List[Node[?]] = n.parents.filter(has)

  private lazy val childrenOf: Map[Node[?], List[Node[?]]] = nodes.flatMap(c => parentsOf(c).map(_ -> c)).groupMap(_._1)(_._2)
  /** The nodes that name `n` as a parent, in the model's order: its parts, and the design decisions below it. */
  def children(n: Node[?]): List[Node[?]] = childrenOf.getOrElse(n, Nil)
  /** The parts of `n` that together refine it: claims, contracts and assumptions under it. */
  def parts(n: Node[?]): List[Node[?]] = children(n).filter(isStatement)
  def isStatement(n: Node[?]): Boolean = n.kind == NodeKind.Claim || n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption

  /** The claims with no parents: one, the root, in a well-formed knowledge base. */
  def roots: List[Node[?]] = nodes.filter(n => n.kind == NodeKind.Claim && n.parents.isEmpty)
  /** The root: the one claim with no parents. */
  def root: Option[Node[?]] = roots match
    case List(r) => Some(r)
    case _       => None
  def definitions: List[Node[?]] = nodes.filter(_.kind == NodeKind.Definition)

  /** Every node above `n` (each once), nearest first. */
  def ancestors(n: Node[?]): List[Node[?]] = Walk.breadthFirst(parentsOf(n), identity)(parentsOf)

  /** Every node after the nodes it rests on: its parents, the definitions it uses, the contracts its code calls. */
  lazy val ordered: List[Node[?]] =
    Walk.postorder(nodes, identity)(n => definitionsUsed(n, provisional) ++ parentsOf(n) ++ calledBy(n))

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
    def returnsIt(c: Node[?]) = c.post.forall(p => p.params.isEmpty || p.params.lastOption.exists(x => holds(x._2)))
    def keeper(c: Node[?]) = c.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    def within(c: Node[?]) = i.scope.isEmpty || (c :: ancestors(c)).exists(a => i.scope.exists(_ eq a))
    nodes.filter { c =>
      within(c) && (c.kind match
        case NodeKind.Contract => returnsIt(c)
        // A design decision governs code no proof covers: it is in scope below a contract that keeps
        // the rule, is exempt from it or returns what it is about, and with no contract above it at all.
        case NodeKind.Design   =>
          val contracts = ancestors(c).filter(_.kind == NodeKind.Contract)
          contracts.isEmpty || contracts.exists(a => keeper(a) || a.kept.exists(_.invariant eq i) || returnsIt(a))
        case _                 => false)
    }

  // ---------------------------------------------------------------------------
  // The vocabulary
  // ---------------------------------------------------------------------------

  /** The contracts and assumptions about each operation, by its name. */
  lazy val onOp: Map[String, List[Node[?]]] = nodes.flatMap(n => n.op.map(_.name -> n)).groupMap(_._1)(_._2)
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
      val picked =
        if ds.size == 1 then ds
        else ds.filter(d => chosen(d.id)) match
          case List(d)       => List(d)
          case _ if fallback => ds.take(1)
          case _             => Nil
      picked.map(t -> _)
    }.toMap

  /** The definitions in force before any is chosen: the first listed of alternatives (how code runs). */
  private[frflow] lazy val provisional: Map[String, Node[?]] = inForce(_ => false, fallback = true)

  /** The definitions in force a node depends on: those of the terms it mentions, and theirs, however nested. */
  def definitionsUsed(n: Node[?], inForce: Map[String, Node[?]]): List[Node[?]] =
    Walk.preorder(termsOf(n).filterNot(n.defines.contains).flatMap(inForce.get), _.id)(d => termsOf(d).flatMap(inForce.get))

  /** The data parameters a lambda reads, through the defines it calls and the definitions of the terms it uses. */
  def reads(l: Lifted[?]): List[String] =
    def go(ps: List[String], seen: Set[String]): List[String] = ps.flatMap { p =>
      if seen(p) then Nil
      else provisional.get(p).flatMap(_.substs.find(_.name == p)).flatMap(_.term).fold(List(p))(t => go(paramsIn(t), seen + p))
    }
    go(paramsIn(l), Set.empty).distinct
  private def paramsIn(l: Lifted[?]): List[String] = (l.paramObjects ++ Def.closure(l.defs).flatMap(_.lifted.paramObjects)).map(_.name).distinct

  /** Every lambda of the nodes and the defines, translated or not. */
  private[frflow] lazy val lifteds: List[Lifted[?]] = nodes.flatMap(_.referenced) ++ defs.map(_.lifted)
  /** The lambdas Lean is given. */
  private[frflow] lazy val formalLifteds: List[Lifted[?]] = nodes.flatMap(_.lifted) ++ defs.map(_.lifted)

  /** Defined functions used anywhere, dependencies first. */
  lazy val defs: List[Def[?]] = Walk.postorder(defRoots, _.name)(_.lifted.defs)
  private def defRoots: List[Def[?]] = nodes.flatMap(_.referenced).flatMap(_.defs) ++ implementations.flatMap(_.proven)
  /** Every `define` reached, each object once: two by one name are two here. */
  private[frflow] lazy val allDefs: List[Def[?]] = Walk.preorder(defRoots, identity)(_.lifted.defs)

  /** Every parameter object reached (operations included), possibly two by one name. */
  private[frflow] lazy val paramObjects: List[Param[?]] =
    lifteds.flatMap(_.paramObjects) ++ nodes.flatMap(_.op) ++ definitions.flatMap(_.substs).flatMap(_.param)
  /** Parameters used anywhere (operations included), by name. */
  lazy val params: List[Param[?]] = paramObjects.distinctBy(_.name).sortBy(_.name)

  /** The opaque types used anywhere, by name. */
  lazy val opaques: List[Opaque] =
    (lifteds.flatMap(_.opaqueObjects) ++ definitions.flatMap(_.substs).map(_.target).collect { case o: Opaque => o })
      .distinctBy(_.name).sortBy(_.name)

  /** Domain types used anywhere, dependencies first. */
  lazy val types: List[TypeDecl] =
    val all = formalLifteds.flatMap(_.types) ++ definitions.flatMap(_.substs).flatMap(_.types)
    // The same type as seen with and without its doc comment: the one with it.
    val byName = all.groupBy(_.name).view.mapValues(ds => ds.maxBy(_.lean.length)).toMap
    Walk.postorder(all.map(_.name).distinct.flatMap(byName.get), _.name)(_.uses.flatMap(byName.get))

  // ---------------------------------------------------------------------------
  // Code
  // ---------------------------------------------------------------------------

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
    KnowledgeBase(name, idea, implementations.filterNot(_.contract == i.contract) :+ i)(nodes*)

  private lazy val byContract = implementations.map(i => i.contract -> i).toMap
  def implementation(n: Node[?]): Option[Implementation] = byContract.get(n.id)

  /** The files the model is written in: those its nodes are defined in, and where implementations are
    * attached. A model may span several files; each holds only the model.
    */
  def modelFiles: List[String] = (nodes.map(_.file) ++ implementations.flatMap(_.modelFile)).filter(_.nonEmpty).distinct

  /** The operations a define calls, through the defines it calls, by name. */
  def opsCalledBy(d: Def[?]): List[String] = Def.closure(List(d)).flatMap(_.lifted.paramObjects).map(_.name).filter(isOp).distinct

  /** The contracts (and assumptions) whose operations a node's proven code calls. */
  def calledBy(n: Node[?]): List[Node[?]] =
    implementation(n).flatMap(_.proven).toList.flatMap(opsCalledBy).distinct.filterNot(p => n.op.exists(_.name == p))
      .flatMap(onOp.getOrElse(_, Nil)).filterNot(_ eq n)

  // ---------------------------------------------------------------------------
  // Running it, and what is wrong with it (see Wiring in Runtime.scala, ExampleRuns, Validation)
  // ---------------------------------------------------------------------------

  /** The running system: the registered implementation of `contract`, reading the given parameter
    * values, with every result checked against the contract (see `enforce`). Every other operation with
    * code is bound to that code's service, every defined term to its definition, and the assumptions
    * whose terms are all bound are checked at start and whenever the values they read change.
    */
  def service[A, B, R](contract: Node[(A, B) => R])(bindings: Binding*): (A, B) => R = Wiring.service(this, contract, bindings)

  /** Each defined parameter bound to its definition (as examples and `service` run them). */
  lazy val definitionBindings: List[Binding] = Wiring.definitionBindings(this)

  /** Each operation bound to its registered code, as examples run it. */
  lazy val opCode: List[Binding] = Wiring.opCode(this)

  /** The assumptions of facts that can be computed, to check where code runs (a quantifier over a type
    * cannot be: such an assumption is trusted only).
    */
  lazy val runtimeAssumptions: List[Assumption] = Wiring.runtimeAssumptions(this)

  /** The results of a node's examples, against the implementation when one is registered, and the
    * generated calls its code fails.
    */
  def exampleResults(n: Node[?]): List[ExampleResult] = ExampleRuns.results(this, n)

  /** The calls beyond the examples (every combination of their inputs, and varied data) whose result
    * breaks the contract.
    */
  def generated(n: Node[?]): List[ExampleResult] = ExampleRuns.generated(this, n)

  /** What a contract does not promise, found mechanically (see `ExampleRuns.limits`). */
  def limits(n: Node[?]): List[String] = ExampleRuns.limits(this, n)

  /** Structural problems; a knowledge base with problems is not checked. */
  lazy val problems: List[Problem] = Validation.problems(this)
