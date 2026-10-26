package frflow
package kb

import frflow.example.ExampleRuns
import frflow.protocol.{NodeKind, RunCheck, RunTime, Walk}
import frflow.runtime.Wiring

/** The idea and its nodes: one root claim refined by a DAG of parts, told apart by identity; `name` is the Lean namespace;
  * `idea`, the file the purpose is written in (`IDEA.md`), if any.
  */
final class KnowledgeBase(val name: String, val idea: String = "", val implementations: List[Implementation] = Nil,
    val generators: List[(LeanType[?], Gen[?])] = Nil, val testing: TestSettings = TestSettings(),
    val onViolation: Violation => Unit = Violation.log)(nodeList: Node[?]*):
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
  /** The types the flows may fail with (the failing boundaries' errors, the contracts' failure clauses): one at most.
    * With one, the proven flows that may fail run in Lean's `ExceptT E (StateM World)`.
    */
  lazy val failureTypes: List[LeanType[?]] =
    (models.flatMap(_.boundary.failure.map(_.termType)) ++ nodes.flatMap(_.failure.map(_.err))).distinctBy(t => Types.walk(t).lean)
  def failureType: Option[LeanType[?]] = failureTypes.headOption
  /** Whether a boundary of the models may fail: the world then holds the faults. */
  def faulty: Boolean = models.exists(_.boundary.fails)
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
  private def defRoots: List[Def[?]] = nodes.flatMap(_.referenced).flatMap(_.defs) ++ implementations.flatMap(_.proven) ++ modelDefs
  /** The defines a model's operations use: Lean's models need them too. */
  private def modelDefs: List[Def[?]] = models.flatMap(mo => mo.boundary.operations.flatMap { m =>
    val bs = m.getParameters.toList.zip(m.getGenericParameterTypes.toList).map((p, t) => Binder(Names.ident(p.getName), LeanType.ofJava(t)))
    scala.util.Try(Lifted(() => (bs, Term(Tree.Do(Steps.of(m.invoke(mo.model, bs.map(_.term[Any])*).asInstanceOf[Flow[?]])._1),
      LeanType.ofJava(m.getGenericReturnType))), null, "").defs).getOrElse(Nil)
  })
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

  /** Registers the code of a contract's operation, built under the values of each example and call (`grants.value`):
    * `implement(share)((by, doc, withWhom) => …)`, a function of the operation's inputs.
    */
  /** `calls`: the operations the code calls (`lookup.value(…)` inside it): FrFlow cannot see into plain code, so the code
    * says so, and its tests check that it calls only those.
    */
  def implement[F](contract: Node[F], calls: Param[?]*): Implementing[F] = Implementing(this, contract, calls.map(_.name).toList)

  /** Code proven to meet the contract. `implementProven(c)(d)`: a `define` (Lean proves every result meets the contract,
    * and the root holds of it, `root_impl`); `implementProven(c)(d, runs)`: production code (a query) beside the proven
    * `define`, checked against it and against the contract; `implementProven(job)((now, …) => for … yield …)`: a flow,
    * proven on the models, named in Lean as the `def` it is (`expireOnce`) and its run as `expireOnce_run`.
    */
  def implementProven[F](contract: Node[F])(using s: Sig[F]): Proving[F, s.Code] = Proving(this, contract)
  def withImplementation(i: Implementation): KnowledgeBase =
    KnowledgeBase(name, idea, implementations.filterNot(_.contract == i.contract) :+ i, generators, testing, onViolation)(nodes*)

  /** Values of `T` for the tests of code against contracts, where the ones derived from the type rarely reach what a
    * contract is about: `.generating(Gen.oneOf(Path("/a"), Path("/b")))`.
    */
  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators :+ (t -> g), testing, onViolation)(nodes*)
  /** How many cases each contract's code is tested on, from which seed. */
  def testedWith(settings: TestSettings): KnowledgeBase = KnowledgeBase(name, idea, implementations, generators, settings, onViolation)(nodes*)
  /** Where a broken contract or assumption is reported before `service` throws: a log line by default; an application
    * adds its own (a metric, an alert) here, and maps the thrown `ContractViolation` to its own failure (an HTTP 500).
    */
  def reporting(report: Violation => Unit): KnowledgeBase = KnowledgeBase(name, idea, implementations, generators, testing, report)(nodes*)

  /** How a contract's code is checked where `service` runs it: as the developer chose (`checkedAtRunTime`), else on every
    * call, unless the running code is the code Lean proves (a proven define's result needs no second look; the values it
    * runs with are still checked against the assumptions).
    */
  def runTime(n: Node[?]): Option[RunTime] =
    // As this knowledge base holds the node: a choice made on it is the one in force, whichever copy is passed.
    val m = node(n.id).getOrElse(n)
    implementation(m).filter(i => !i.flow && m.post.isDefined).map { i =>
      val check = m.runCheck.getOrElse(if i.provenCode then RunCheck.Never else RunCheck.EveryCall)
      RunTime(check, if m.local.isDefined then "its check (checkedBy)" else "the contract", m.runCheck.isDefined)
    }
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
  def service[F](contract: Node[F])(bindings: Binding*): F = Wiring.service(this, contract, bindings)
  /** The running system of a flow: its proven code in `F` (`run[IO](expiryJob)(db.bind(sqlite))`), calling the bound
    * implementations of its boundaries; the operations it calls run as their services.
    */
  def run[G[_]: cats.effect.kernel.Sync]: Runner[G] = Runner(this)
  lazy val definitionBindings: List[Binding] = Wiring.definitionBindings(this)
  lazy val opCode: List[Binding] = Wiring.opCode(this)
  lazy val runtimeAssumptions: List[Assumption] = Wiring.runtimeAssumptions(this)
  def exampleResults(n: Node[?]): List[ExampleResult] = ExampleRuns.results(this, n)
  /** Its code tested against the contract (plain code, or code beside a proven define); none when its code is proven or a flow. */
  def test(n: Node[?], replay: List[Testing.Replay] = Nil, settings: TestSettings = testing): Option[Testing.Report] =
    Testing.run(this, n, settings, replay)
  /** Structural problems; a knowledge base with problems is not checked. */
  lazy val problems: List[Problem] = Validation.problems(this)
