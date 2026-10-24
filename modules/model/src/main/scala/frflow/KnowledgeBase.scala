package frflow

import frflow.protocol.{NodeKind, Walk, tooFew}
import java.util.regex.Pattern.quote

/** The idea and its nodes: one root claim refined by a DAG of parts, told apart by identity; `name` is the Lean namespace. */
final class KnowledgeBase(val name: String, val idea: String, val implementations: List[Implementation] = Nil,
    val generators: List[(LeanType[?], Gen[?])] = Nil, val testing: TestSettings = TestSettings())(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList
  private lazy val members: Set[Node[?]] = nodes.toSet
  def has(n: Node[?]): Boolean = members(n)
  private lazy val byId: Map[String, Node[?]] = nodes.reverse.map(n => n.id -> n).toMap
  def node(id: String): Option[Node[?]] = byId.get(id)
  def parentsOf(n: Node[?]): List[Node[?]] = n.parents.filter(has)
  private lazy val childrenOf: Map[Node[?], List[Node[?]]] = nodes.flatMap(c => parentsOf(c).map(_ -> c)).groupMap(_._1)(_._2)
  /** In the model's order: its parts, and the design decisions below it. */
  def children(n: Node[?]): List[Node[?]] = childrenOf.getOrElse(n, Nil)
  def parts(n: Node[?]): List[Node[?]] = children(n).filter(isStatement)
  def isRoot(n: Node[?]): Boolean = root.exists(_ eq n)
  /** A boundary's model is decided, not stated in Lean: it is what proven flows are proven from. */
  def isStatement(n: Node[?]): Boolean =
    n.kind == NodeKind.Claim || n.kind == NodeKind.Contract || (n.kind == NodeKind.Assumption && n.modelOf.isEmpty)
  /** Each boundary with the model it is decided to behave as. */
  lazy val models: List[ModelOf] = nodes.flatMap(_.modelOf)
  def roots: List[Node[?]] = nodes.filter(n => n.kind == NodeKind.Claim && n.parents.isEmpty)
  def root: Option[Node[?]] = roots.headOption.filter(_ => roots.size == 1)
  def definitions: List[Node[?]] = nodes.filter(_.kind == NodeKind.Definition)
  /** Nearest first. */
  def ancestors(n: Node[?]): List[Node[?]] = Walk.breadthFirst(parentsOf(n), identity)(parentsOf)

  /** Every node after its parents, the definitions it uses and the contracts its code calls. */
  lazy val ordered: List[Node[?]] =
    Walk.postorder(nodes, identity)(n => definitionsUsed(n, provisional) ++ parentsOf(n) ++ calledBy(n))

  /** Within its scope: the contracts whose result can hold what the rule is about, and the designs below them. */
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
        // It governs code no proof covers: below a contract the rule reaches, or with no contract above it.
        case NodeKind.Design   =>
          val contracts = ancestors(c).filter(_.kind == NodeKind.Contract)
          contracts.isEmpty || contracts.exists(a => keeper(a) || a.kept.exists(_.invariant eq i) || returnsIt(a))
        case _                 => false)
    }
  lazy val onOp: Map[String, List[Node[?]]] = nodes.flatMap(n => n.op.map(_.name -> n)).groupMap(_._1)(_._2)
  def isOp(name: String): Boolean = onOp.contains(name)

  def termsOf(n: Node[?]): List[String] =
    val ls = n.referenced ++ Def.closure(n.referenced.flatMap(_.defs)).map(_.lifted)
    (ls.flatMap(_.opaques) ++ ls.flatMap(_.paramObjects.map(_.name)) ++ n.op.map(_.name).toList ++
      n.kept.filter(_.view.nonEmpty).flatMap(k => k.invariant.rule.toList.flatMap(_.opaques))).distinct
  lazy val definitionsOf: Map[String, List[Node[?]]] = definitions.flatMap(d => d.defines.map(_ -> d)).groupMap(_._1)(_._2)

  /** Each term's only definition, or the one `chosen` among alternatives; with `fallback`, the first listed. */
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
  private[frflow] lazy val provisional: Map[String, Node[?]] = inForce(_ => false, fallback = true)
  def definitionsUsed(n: Node[?], inForce: Map[String, Node[?]]): List[Node[?]] =
    Walk.preorder(termsOf(n).filterNot(n.defines.contains).flatMap(inForce.get), _.id)(d => termsOf(d).flatMap(inForce.get))

  /** The data parameters a lambda reads, also through the defines and the definitions it uses. */
  def reads(l: Lifted[?]): List[String] =
    def go(ps: List[String], seen: Set[String]): List[String] = ps.flatMap { p =>
      if seen(p) then Nil
      else provisional.get(p).flatMap(_.substs.find(_.name == p)).flatMap(_.term).fold(List(p))(t => go(paramsIn(t), seen + p))
    }
    go(paramsIn(l), Set.empty).distinct
  private def paramsIn(l: Lifted[?]): List[String] = (l.paramObjects ++ Def.closure(l.defs).flatMap(_.lifted.paramObjects)).map(_.name).distinct
  private[frflow] lazy val lifteds: List[Lifted[?]] = nodes.flatMap(_.referenced) ++ defs.map(_.lifted)
  lazy val defs: List[Def[?]] = Walk.postorder(defRoots, _.name)(_.lifted.defs)
  private def defRoots: List[Def[?]] = nodes.flatMap(_.referenced).flatMap(_.defs) ++ implementations.flatMap(_.proven)
  /** Each object once: two by one name are two here. */
  private[frflow] lazy val allDefs: List[Def[?]] = Walk.preorder(defRoots, identity)(_.lifted.defs)
  private[frflow] lazy val paramObjects: List[Param[?]] =
    lifteds.flatMap(_.paramObjects) ++ nodes.flatMap(_.op) ++ definitions.flatMap(_.substs).flatMap(_.param)
  lazy val params: List[Param[?]] = paramObjects.distinctBy(_.name).sortBy(_.name)
  lazy val opaques: List[Opaque] =
    (lifteds.flatMap(_.opaqueObjects) ++ definitions.flatMap(_.substs).map(_.target).collect { case o: Opaque => o })
      .distinctBy(_.name).sortBy(_.name)

  lazy val types: List[TypeDecl] =
    // The boundaries' operations and the models' states are typed in Lean too.
    val boundaryTypes = models.flatMap(m => m.model.stateType :: m.boundary.operations.flatMap(o =>
      LeanType.ofJava(o.getGenericReturnType) :: o.getGenericParameterTypes.toList.map(LeanType.ofJava)))
    val all = lifteds.flatMap(_.types) ++ definitions.flatMap(_.substs).flatMap(_.types) ++ boundaryTypes.flatMap(_.types)
    // The same type as seen with and without its doc comment: the one with it.
    val byName = all.groupBy(_.name).view.mapValues(ds => ds.maxBy(_.lean.length)).toMap
    Walk.postorder(all.map(_.name).distinct.flatMap(byName.get), _.name)(_.uses.flatMap(byName.get))

  /** Registers the code of a contract's operation, built under the values of each example and call (`grants.value`). */
  /** `calls`: the operations the code calls (`lookup.value(…)` inside it): FrFlow cannot see into plain code, so the code
    * says so, and its tests check that it calls only those.
    */
  inline def implement[A, B, R](contract: Node[(A, B) => R], calls: Param[?]*)(inline impl: (A, B) => R): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => impl, Source.sourceFiles(impl), Source.sources(impl).mkString,
      calls = calls.map(_.name).toList))

  /** Code written as a `define`: Lean proves every result meets the contract, and the root holds of it (`root_impl`). */
  inline def implementProven[A, B, R](contract: Node[(A, B) => R])(inline impl: Def[(A, B) => R]): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => impl.lifted.value, Source.sourceFiles(impl), "", Some(impl)))

  /** Production code (`runs`: a query) beside the proven `define`, checked against it and against the contract. */
  inline def implementProven[A, B, R](contract: Node[(A, B) => R])(inline impl: Def[(A, B) => R], inline runs: (A, B) => R): KnowledgeBase =
    withImplementation(Implementation(contract.id, () => runs, Source.sourceFiles(runs), Source.sources(runs).mkString, Some(impl)))
  /** A flow attached as a contract's code: Lean proves every run of it on the models meets the contract. Named in Lean
    * as the `def` it is (`expireOnce`), its run on the models as `expireOnce_run`.
    */
  inline def implementProven[A, R](contract: Node[A => Flow[R]])(inline impl: Term[A] => Flow[R]): KnowledgeBase =
    withImplementation(Implementation.ofFlow(contract, impl, Source.text(impl), Source.sourceFiles(impl)))
  def withImplementation(i: Implementation): KnowledgeBase =
    KnowledgeBase(name, idea, implementations.filterNot(_.contract == i.contract) :+ i, generators, testing)(nodes*)

  /** Values of `T` for the tests of code against contracts, where the ones derived from the type rarely reach what a
    * contract is about: `.generating(Gen.oneOf(Path("/a"), Path("/b")))`.
    */
  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators :+ (t -> g), testing)(nodes*)
  /** How many cases each contract's code is tested on, from which seed. */
  def testedWith(settings: TestSettings): KnowledgeBase = KnowledgeBase(name, idea, implementations, generators, settings)(nodes*)
  private lazy val byContract = implementations.map(i => i.contract -> i).toMap
  def implementation(n: Node[?]): Option[Implementation] = byContract.get(n.id)
  def modelFiles: List[String] = (nodes.map(_.file) ++ implementations.flatMap(_.modelFile)).filter(_.nonEmpty).distinct
  def opsCalledBy(d: Def[?]): List[String] = Def.closure(List(d)).flatMap(_.lifted.paramObjects).map(_.name).filter(isOp).distinct

  def calledBy(n: Node[?]): List[Node[?]] =
    implementation(n).flatMap(_.proven).toList.flatMap(opsCalledBy).distinct.filterNot(p => n.op.exists(_.name == p))
      .flatMap(onOp.getOrElse(_, Nil)).filterNot(_ eq n)

  /** The running system: the code of `contract`, every result checked against it; the operations it calls bound
    * to their services, and the assumptions whose terms are bound checked whenever the values they read change.
    */
  def service[A, B, R](contract: Node[(A, B) => R])(bindings: Binding*): (A, B) => R = Wiring.service(this, contract, bindings)
  /** The running system of a flow: its proven code in `F` (`run[IO](expiryJob)(db.bind(sqlite))`), calling the bound
    * implementations of its boundaries; the operations it calls run as their services.
    */
  def run[F[_]: cats.effect.kernel.Sync]: Runner[F] = Runner(this)
  lazy val definitionBindings: List[Binding] = Wiring.definitionBindings(this)
  lazy val opCode: List[Binding] = Wiring.opCode(this)
  lazy val runtimeAssumptions: List[Assumption] = Wiring.runtimeAssumptions(this)
  def exampleResults(n: Node[?]): List[ExampleResult] = ExampleRuns.results(this, n)
  /** Its code tested against the contract (plain code, or code beside a proven define); none when its code is proven or a flow. */
  def test(n: Node[?], replay: List[Testing.Replay] = Nil): Option[Testing.Report] = Testing.run(this, n, testing, replay)
  /** Structural problems; a knowledge base with problems is not checked. */
  lazy val problems: List[Problem] = Validation.problems(this)

/** What keeps a knowledge base from being checked, said so that its author can fix it. */
enum Problem(val message: String):
  case Structure(text: String) extends Problem(text)
  case Vocabulary(text: String) extends Problem(text)
  case Wording(text: String) extends Problem(text)
  case Examples(text: String) extends Problem(text)
  case Invariants(text: String) extends Problem(text)
  case Code(text: String) extends Problem(text)
  override def toString: String = message

private[frflow] object Validation:
  import Problem.*
  def problems(kb: KnowledgeBase): List[Problem] =
    structure(kb) ++ vocabulary(kb) ++ names(kb) ++ wording(kb) ++ examples(kb) ++ invariants(kb) ++ code(kb)
  private def isOperation(n: Node[?]) = n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption

  private def structure(kb: KnowledgeBase): List[Problem] =
    import kb.{nodes, parentsOf}
    val ids = nodes.map(_.id)
    // The operations some code calls (plain code calls one through its parameter: `decide.value(...)`, `decide(...)`).
    val called = kb.implementations.flatMap(_.proven).flatMap(kb.opsCalledBy).toSet ++ kb.implementations.flatMap(_.calls) ++
      kb.onOp.keySet.filter(o => kb.implementations.exists(i => s"\\b${quote(o)}\\b".r.findFirstIn(i.wiring).isDefined))
    def under(kind: NodeKind)(n: Node[?]) = parentsOf(n).exists(_.kind == kind)
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      kb.roots match
        case List(_) => Nil
        // A new project has no nodes while the idea is being written: the root comes first once there are any.
        case Nil if nodes.isEmpty => Nil
        case Nil     => List("a root is required: one claim with no parents, the idea's purpose")
        case rs      => List(s"one root only: ${rs.map(_.id).mkString(", ")} are claims with no parents; put all but one under the nodes they help prove"),
      nodes.filter(n => kb.ancestors(n).exists(_ eq n)).map(n => s"${n.id} is above itself: what it is a part of must not lead back to it"),
      nodes.filter(n => isOperation(n) && n.parents.isEmpty && !n.op.exists(o => called(o.name)) && n.modelOf.isEmpty &&
          !kb.implementation(n).exists(_.flow))
        .map(n => s"${n.id} has no parents: a ${n.kind.toString.toLowerCase} is a part of the nodes it helps prove, unless code calls its operation"),
      nodes.filter(n => n.kind == NodeKind.Design && n.parents.isEmpty).map(n => s"${n.id}: a design decision is under the nodes it serves (.under)"),
      nodes.filter(n => n.kind == NodeKind.Definition && n.parents.nonEmpty).map(n => s"${n.id}: a definition has no parents"),
      nodes.flatMap(n => n.parents.filterNot(kb.has).map(p => s"${n.id}: its parent ${p.id} is not in the knowledge base")),
      nodes.filter(n => n.kind != NodeKind.Design && under(NodeKind.Design)(n))
        .map(n => s"${n.id}: a design decision has no statement to refine; only design decisions go below it"),
      nodes.filter(under(NodeKind.Definition)).map(n => s"${n.id}: nothing is under a definition; a node uses its terms")
    ).flatten.map(Structure(_))

  private def vocabulary(kb: KnowledgeBase): List[Problem] =
    import kb.{definitions, nodes}
    List(
      definitions.filter(_.substs.isEmpty).map(n => s"${n.id}: a definition fixes at least one term"),
      definitions.flatMap(d => d.defines.diff(d.defines.distinct).distinct.map(t => s"${d.id} defines $t twice")),
      definitions.filter(d => kb.definitionsUsed(d, kb.provisional).exists(_ eq d)).map(d => s"${d.id}: its terms are defined through themselves"),
      definitions.flatMap(d => d.defines.filter(kb.isOp).map(t => s"${d.id} defines $t, an operation: code implements an operation, a definition does not")),
      // Something exists of a type holding an Int or Long: Lean's integers are unbounded, so it may not in Scala.
      definitions.flatMap { d =>
        d.substs.filter(s => s.isType && s.types.exists(t => """:\s*(Int|Long)\b""".r.findFirstIn(t.scala).isDefined)).flatMap { s =>
          val ex = s"∃ \\([^)]*: ${quote(s.name)}\\)".r
          nodes.flatMap(_.referenced).find(l => ex.findFirstIn(l.body).isDefined).map(_ =>
            s"${d.id}: ${s.name} := ${s.lean}, whose values hold an Int or Long, but something says one exists: Lean's integers are unbounded, Scala's are not; use BigInt")
        }
      }
    ).flatten.map(Vocabulary(_))

  private def names(kb: KnowledgeBase): List[Problem] =
    val ids = kb.nodes.map(_.id)
    val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r
    val declared = kb.types.map(_.name) ++ kb.defs.map(_.name)
    val terms = kb.params.map(_.name) ++ kb.opaques.map(_.name)
    def twice[A](xs: List[A], name: A => String)(say: (String, List[A]) => String): List[String] =
      xs.distinct.groupBy(name).collect { case (n, as) if as.size > 1 => say(n, as) }.toList
    List(
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      ids.filter(i => i == "Lemmas" || i == "RootImpl").map(i => s"node id $i is reserved in lean/"),
      ids.filter(_ == "IDEA").map(_ => "node id IDEA is reserved: the ledger keeps the decision on IDEA.md under it"),
      // Lean would prove one while Scala runs the other.
      twice(kb.allDefs, _.name)((n, _) => s"two different definitions are named $n (in different packages, say): Lean would know only one of them; rename one"),
      twice(kb.paramObjects, _.name)((p, ps) => s"two different parameters are named $p: ${ps.map(_.means).mkString("; ")}; rename one").sorted,
      twice(kb.lifteds.flatMap(_.opaqueObjects), _.name)((o, _) => s"two different opaque types are named $o; rename one").sorted,
      kb.opaques.map(_.name).filterNot((kb.lifteds.flatMap(_.opaques) ++ kb.definitions.flatMap(_.defines)).contains)
        .map(n => s"opaque type $n: the val name and the name given to Opaque differ"),
      ids.filter(i => declared.contains(i) || terms.contains(i)).map(i => s"node id $i clashes with a type, function or term of the same name"),
      terms.filter(declared.contains).distinct.map(n => s"term $n clashes with a type or function of the same name"),
      kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).map(_._1).distinct.filterNot(n => kb.params.exists(_.name == n))
        .map(n => s"parameter $n: the val name and the name given to Param differ"),
      kb.lifteds.flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.body).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten.map(Vocabulary(_))

  private def wording(kb: KnowledgeBase): List[Problem] =
    List(
      kb.nodes.filter(_.why.trim.isEmpty).map(n => s"${n.id}: say why (the reason for this node)"),
      (kb.params.filter(_.means.trim.isEmpty).map(_.name) ++ kb.opaques.filter(_.means.trim.isEmpty).map(_.name))
        .map(n => s"$n: say what it means in the world"),
      kb.nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement")
    ).flatten.map(Wording(_))

  private def examples(kb: KnowledgeBase): List[Problem] =
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    List(
      kb.nodes.filter(n => n.cases.nonEmpty && n.post.isEmpty).map(n => s"${n.id}: only contracts and assumptions on an operation have examples"),
      contracts.filterNot(n => n.cases.exists(_.expected) && n.cases.exists(!_.expected))
        .map(n => s"${n.id}: a contract needs examples: at least one expect (what it must allow) and one reject"),
      // An implementation that always returns the same value must fail some example.
      contracts.flatMap { n =>
        n.cases.filter(_.expected).map(_.result).distinct match
          case List(v) if !n.cases.exists(e => !e.expected && e.result == v) =>
            List(s"${n.id}: every expect returns ${Example.show(v)}, so an implementation that always returns it would pass the examples; add an expect with another result")
          case _ => Nil
      }
    ).flatten.map(Examples(_))

  private def invariants(kb: KnowledgeBase): List[Problem] =
    import kb.nodes
    val rules = nodes.filter(_.isInvariant)
    def keeps(n: Node[?], i: Node[?]) = n.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    List(
      nodes.flatMap(n => n.kept.map(_.invariant).filterNot(i => kb.has(i) && i.isInvariant)
        .map(i => s"${n.id} keeps ${i.id}, which is not an invariant of this knowledge base")),
      nodes.filter(n => n.kept.exists(_.view.nonEmpty) && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts keep invariants"),
      nodes.filter(n => n.kept.nonEmpty && n.kind != NodeKind.Contract && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: only contracts and design decisions are exempt from invariants"),
      nodes.flatMap(n => n.kept.groupBy(_.invariant.id).collect { case (i, ks) if ks.size > 1 => s"${n.id} names $i more than once" }),
      nodes.flatMap(n => n.kept.filter(k => k.view.isEmpty && tooFew(k.exempt))
        .map(k => s"${n.id}: say in a few words why ${k.invariant.id} does not apply to it")),
      rules.flatMap(i => kb.inScope(i).filterNot(_.kept.exists(_.invariant eq i))
        .map(c => if c.kind == NodeKind.Design then s"${c.id}: say why ${i.id} does not apply to the code it governs (.exempt): a design decision in its scope does"
          else s"${c.id}: keep ${i.id} (.keeps) or say why it does not apply (.exempt): every contract in its scope does one")),
      rules.filterNot(i => nodes.exists(keeps(_, i))).map(i => s"${i.id}: no contract keeps this invariant"),
      rules.flatMap(i => i.scope.filterNot(kb.has).map(s => s"${i.id}: its scope ${s.id} is not in the knowledge base"))
    ).flatten.map(Invariants(_))

  private def code(kb: KnowledgeBase): List[Problem] =
    val boundaries = kb.implementations.flatMap(_.flowDef).flatMap(_.lifted.boundaries).distinct
    List(
      boundaries.filterNot(b => kb.models.exists(_.boundary eq b))
        .map(b => s"the boundary ${b.name}: proven flows call it, so decide what it does (Node.assumption(${b.name})(SomeModel)(…))"),
      kb.models.groupBy(_.boundary).collect { case (b, ms) if ms.size > 1 => s"the boundary ${b.name} has ${ms.size} models: decide one" }.toList,
      kb.models.filterNot(m => m.boundary.cls.isInstance(m.model)).map(m => s"${m.model.lean} is not an implementation of ${m.boundary.cls.getSimpleName}"),
      kb.implementations.flatMap(_.flowDef).filter(d => d.lifted.built._2.termTree match { case Tree.Do(s) => Steps.effectful(s); case _ => false })
        .map(d => s"${d.name}: a proven flow takes no step of the outside world (Flow.effect): call a boundary"),
      // Code that calls its own operation would be proven assuming what it proves.
      kb.nodes.flatMap(c => c.op.filter(o => kb.implementation(c).flatMap(_.proven).exists(d => kb.opsCalledBy(d).contains(o.name)))
        .map(o => s"${c.id}: its implementation calls ${o.name} itself: it cannot be proven from its own promise")),
      kb.implementations.map(_.contract).filterNot(c => kb.nodes.exists(n => n.id == c && n.op.isDefined))
        .map(c => s"implementation of $c: not a contract (or an assumption on an operation) of this knowledge base")
    ).flatten.map(Code(_))
