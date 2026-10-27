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
    val onViolation: Violation => Unit = Violation.log, val written: List[Written] = Nil)(nodeList: Node[?]*):
  val nodes: List[Node[?]] = nodeList.toList
  private lazy val members: Set[Node[?]] = nodes.toSet
  def has(n: Node[?]): Boolean = members(n)
  private lazy val byId: Map[String, Node[?]] = nodes.reverse.map(n => n.id -> n).toMap
  def node(id: String): Option[Node[?]] = byId.get(id)
  /** What it is a part of, and what it is a premise of (`.assuming`). */
  def parentsOf(n: Node[?]): List[Node[?]] = n.parents.filter(has) ++ premiseOf.getOrElse(n, Nil)
  private lazy val premiseOf: Map[Node[?], List[Node[?]]] =
    nodes.flatMap(c => premisesOf(c).map(_ -> c)).groupMap(_._1)(_._2)
  /** The assumptions a node rests on: those it names (`.assuming`), and a fact naming it as what a store starts
    * satisfying (`storedBookings.startsSatisfying(neverOverlap)`, written after the claim it names).
    */
  def premisesOf(n: Node[?]): List[Node[?]] =
    (n.premises.filter(has) ++ startsOf.getOrElse(n, Nil)).distinctBy(System.identityHashCode)
  private lazy val startsOf: Map[Node[?], List[Node[?]]] =
    nodes.flatMap(f => f.startsSatisfying.map(_ -> f)).groupMap(_._1)(_._2)
  private lazy val childrenOf: Map[Node[?], List[Node[?]]] = nodes.flatMap(c => parentsOf(c).map(_ -> c)).groupMap(_._1)(_._2)
  /** In the model's order: its parts, and the design decisions below it. */
  def children(n: Node[?]): List[Node[?]] = childrenOf.getOrElse(n, Nil)
  def parts(n: Node[?]): List[Node[?]] = children(n).filter(isStatement)
  def isRoot(n: Node[?]): Boolean = roots.exists(_ eq n)
  /** A boundary's model is decided, not stated in Lean: it is what proven flows are proven from. Nor is a fact of how
    * the system is run (`stored.writtenOnlyBy(book)`): FrFlow reads it, Lean has nothing to say of it.
    */
  def isStatement(n: Node[?]): Boolean =
    n.kind == NodeKind.Claim || n.kind == NodeKind.Contract ||
      (n.kind == NodeKind.Assumption && n.modelOf.isEmpty && n.fact.isEmpty)
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
  /** The root statements, a small set the author keeps concise: each claim or contract no node is above and no code
    * calls (a contract on a flow among them: a service's purpose, stated of its run).
    */
  def roots: List[Node[?]] =
    nodes.filter(n => n.parents.isEmpty && (n.kind == NodeKind.Claim ||
      (n.kind == NodeKind.Contract && !n.op.exists(o => calledOps(o.name)))))
  /** The first root claim (the first root, if none is a claim): the one the idea's title and lead are the purpose
    * of.
    */
  def root: Option[Node[?]] = roots.find(_.kind == NodeKind.Claim).orElse(roots.headOption)
  /** The operations some code calls (plain code calls one through its parameter: `decide.value(...)`,
    * `decide(...)`).
    */
  lazy val calledOps: Set[String] =
    implementations.flatMap(_.proven).flatMap(opsCalledBy).toSet ++ implementations.flatMap(_.calls) ++
      onOp.keySet.filter(o =>
        implementations.exists(i => s"\\b${java.util.regex.Pattern.quote(o)}\\b".r.findFirstIn(i.wiring).isDefined))
  def definitions: List[Node[?]] = nodes.filter(_.kind == NodeKind.Definition)
  /** The `always` claims about values of a type, each with its rule: what every value of the type that can be made
    * holds.
    */
  lazy val typeInvariants: List[(Node[?], Def[?])] =
    nodes.flatMap(n => n.always.filter(_.store.isEmpty).map(n -> _.rule))
  /** The `always` claims about a store's states, each with its rule. */
  def storeRules(m: StateModel[?]): List[(Node[?], Def[?])] =
    nodes.flatMap(n => n.always.filter(_.store.exists(_ eq m)).map(n -> _.rule))
  /** The invariants a value of type `t` holds: of its type, for a list of its elements', and within a record of its
    * fields'.
    */
  def invariantsOn(t: LeanType[?]): List[(Node[?], Def[?], Reach)] =
    if typeInvariants.isEmpty then Nil
    else onType.synchronized(onType.computeIfAbsent(t, u => invariantsOn(Types.walk(u).lean)))
  private val onType = new java.util.IdentityHashMap[LeanType[?], List[(Node[?], Def[?], Reach)]]()
  /** The same, of a type as Lean writes it. */
  def invariantsOn(lean: String): List[(Node[?], Def[?], Reach)] = within(lean, Set.empty)
  private def within(lean: String, seen: Set[String]): List[(Node[?], Def[?], Reach)] =
    val direct = ruleTypes.flatMap { (n, d, of) =>
      if of == lean then List((n, d, Reach.It)) else if lean == s"(List $of)" then List((n, d, Reach.Each)) else Nil
    }
    val fields = if seen(lean) then Nil else records.getOrElse(lean, Nil).zipWithIndex.flatMap { case ((f, t), i) =>
      within(t, seen + lean).map((n, d, r) => (n, d, Reach.Field(f, i, r)))
    }
    direct ++ fields
  private lazy val ruleTypes = typeInvariants.map((n, d) => (n, d, Types.walk(d.lifted.built._1.head.tpe).lean))
  /** The records' fields, as Lean names and types. */
  private lazy val records: Map[String, List[(String, String)]] =
    types.filter(_.body.startsWith("structure")).flatMap(t => t.ctors.headOption.map(c => t.name -> c._2)).toMap
  /** Whether a value of type `t` holds the invariants of its type (and its parts those of theirs), run as Scala. */
  def holds(t: LeanType[?])(v: Any): Boolean = invariantsOn(t).forall { (_, d, reach) =>
    // A `forall` over numbers ranges over the value's own numbers and their neighbours; a rule Scala cannot run
    // still (a `forall` over another type) refuses nothing here.
    scala.util.Try(Watch.within(Watch.overNumbers(List(v)))(reach.holds(v, d.fn.asInstanceOf[Any => Boolean])))
      .getOrElse(true)
  }
  /** What always holds of what a model holds in a world: the rules of its state's type, and its store's. */
  def worldRules(m: ModelOf): List[(Node[?], Def[?], Reach)] =
    invariantsOn(m.model.stateType) ++ storeRules(m.model).map((n, d) => (n, d, Reach.It))
  /** The programs that write what an `always` claim is about, each by the first statement on it its proven flow meets:
    * the flows calling a boundary whose model holds it.
    */
  def writers(n: Node[?]): List[Node[?]] =
    val holding = models.filter(m => worldRules(m).exists(_._1 eq n)).map(_.boundary).toSet
    nodes.flatMap(c => implementation(c).filter(i => i.flowDef.exists(_.lifted.boundaries.exists(holding))).map(c -> _))
      .distinctBy((_, i) => i.flowDef.map(_.name)).map(_._1)
  /** What a statement quantifies over: its formula's variables, its call's inputs and result, and the states of the
    * models a flow runs on.
    */
  def boundTypes(n: Node[?]): List[LeanType[?]] =
    val formula = n.formula.toList.flatMap(_.built._2.termTree match
      case Tree.Quant(true, bs, _) => bs.map(_.tpe)
      case _                       => Nil)
    val call = n.post.toList.flatMap(_.built._1.map(_.tpe)).filterNot(_.shape == frflow.types.Shape.WorldT)
    formula ++ call ++ (if n.isFlow then models.map(_.model.stateType) else Nil)
  /** The invariants of types a statement assumes: those on what it quantifies over. */
  def invariantsUsedBy(n: Node[?]): List[Node[?]] =
    if !isStatement(n) || n.isAlways then Nil
    else
      val stores = if n.isFlow then models.flatMap(m => storeRules(m.model).map(_._1)) else Nil
      (boundTypes(n).flatMap(invariantsOn).map(_._1) ++ stores).distinctBy(_.id)
  /** Nearest first. */
  def ancestors(n: Node[?]): List[Node[?]] = Walk.breadthFirst(parentsOf(n), identity)(parentsOf)

  /** Every node after its parents, the definitions it uses and the contracts its code calls. */
  lazy val ordered: List[Node[?]] =
    Walk.postorder(nodes, identity)(n => usedAbove(n, provisional) ++ parentsOf(n) ++ calledBy(n))

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
    Walk.preorder(termsOf(n).filterNot(n.defines.contains).flatMap(inForce.get), _.id)(d =>
      termsOf(d).flatMap(inForce.get)) ++
      invariantsUsedBy(n)
  /** What a node uses that is above it, decided before it. What is below it (a premise it names, `.assuming`, such as
    * an `always` assumption of what comes from outside, whose rule its Lean takes) is decided after it, as its part:
    * it is not also what the node uses, or a premise would be both above and below it, each waiting for the other.
    */
  def usedAbove(n: Node[?], inForce: Map[String, Node[?]]): List[Node[?]] =
    val below = Walk.preorder(children(n), System.identityHashCode)(children)
    definitionsUsed(n, inForce).filterNot(d => below.exists(_ eq d))

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
  private def defRoots: List[Def[?]] =
    nodes.flatMap(_.referenced).flatMap(_.defs) ++
      nodes.flatMap(n => n.holds ++ n.initially) ++
      implementations.flatMap(_.proven) ++ modelDefs
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
    * `implementTested(share)((by, doc, withWhom) => …)`, a function of the operation's inputs.
    */
  /** `calls`: the operations the code calls (`lookup.value(…)` inside it): FrFlow cannot see into plain code, so the code
    * says so, and its tests check that it calls only those.
    */
  def implementTested[F](contract: Node[F], calls: Param[?]*): Implementing[F] =
    Implementing(this, contract, calls.map(_.name).toList)
  /** Plain Scala code giving `d` its meaning, tested against the claims on it that nothing below proves (the others are
    * proven from those): `implementTested(granted)((held, request) => Calendar(held).grants(request))`.
    */
  def implementTested[F](d: Definition[F], calls: Param[?]*): Defining[F] = Defining(this, d, calls.map(_.name).toList)
  /** The claims stated of one Definition (or Declaration): its operation's. */
  def claimsOn(d: Param[?]): List[Node[?]] = nodes.filter(n => n.onOperation && n.op.exists(_ eq d))
  /** Registers code for `d`: a copy for each claim on it that `check` holds it to (all, or those nothing below
    * proves).
    */
  private[frflow] def withDefinition(d: Param[?], i: Implementation, leavesOnly: Boolean): KnowledgeBase =
    val held = claimsOn(d).filter(c => !leavesOnly || parts(c).isEmpty)
    val is =
      if held.isEmpty then List(i.copy(contract = "", definition = Some(d.name)))
      else held.map(c => i.copy(contract = c.id, definition = Some(d.name)))
    val others = implementations.filterNot(_.definition.contains(d.name))
    KnowledgeBase(name, idea, others ++ is, generators, testing, onViolation, written)(nodes*)
  /** Whether code gives `d` its meaning. */
  def defines(d: Param[?]): Boolean =
    implementations.exists(_.definition.contains(d.name)) || claimsOn(d).exists(implementation(_).isDefined)

  /** Code proven to meet the contract. `implementProven(c)(d)`: a `define` (Lean proves every result meets the contract,
    * and the root holds of it, `root_impl`); `implementProven(c)(d, runs)`: production code (a query) beside the proven
    * `define`, checked against it and against the contract; `implementProven(job)((now, …) => for … yield …)`: a flow,
    * proven on the models, named in Lean as the `def` it is (`expireOnce`) and its run as `expireOnce_run`.
    */
  def implementProven[F](contract: Node[F])(using s: Sig[F]): Proving[F, s.Code] = Proving(this, contract)
  /** Proven code giving `d` its meaning: a flow over its inputs (`implementProven(book)(bookIfGranted)`), or a
    * `define`.
    * Lean proves it meets every claim on `d`.
    */
  def implementProven[F](d: Definition[F])(using s: Sig[F]): ProvingDefinition[F, s.Code] = ProvingDefinition(this, d)
  def withImplementation(i: Implementation): KnowledgeBase =
    val others = implementations.filterNot(_.contract == i.contract)
    KnowledgeBase(name, idea, others :+ i, generators, testing, onViolation, written)(nodes*)

  /** Values of `T` for the tests of code against contracts, where the ones derived from the type rarely reach what a
    * contract is about: `.generating(Gen.oneOf(Path("/a"), Path("/b")))`.
    */
  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators :+ (t -> g), testing, onViolation, written)(nodes*)
  /** How many cases each contract's code is tested on, from which seed. */
  def testedWith(settings: TestSettings): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators, settings, onViolation, written)(nodes*)
  /** Where a broken contract or assumption is reported before `service` throws: a log line by default; an application
    * adds its own (a metric, an alert) here, and maps the thrown `ContractViolation` to its own failure (an HTTP 500).
    */
  def reporting(report: Violation => Unit): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators, testing, report, written)(nodes*)

  /** How a contract's code is checked where `service` runs it: as the developer chose (`checkedAtRunTime`), else on every
    * call, unless the running code is the code Lean proves (a proven define's result needs no second look; the values it
    * runs with are still checked against the assumptions). The code of a Definition is not checked where it runs: proofs
    * and tests check it before production (`None`).
    */
  def runTime(n: Node[?]): Option[RunTime] =
    // As this knowledge base holds the node: a choice made on it is the one in force, whichever copy is passed.
    val m = node(n.id).getOrElse(n)
    implementation(m).filter(i => !i.flow && i.definition.isEmpty && m.post.isDefined).map { i =>
      val check = m.runCheck.getOrElse(if i.provenCode then RunCheck.Never else RunCheck.EveryCall)
      RunTime(check, if m.local.isDefined then "its check (checkedBy)" else "the contract", m.runCheck.isDefined)
    }
  private lazy val byContract = implementations.map(i => i.contract -> i).toMap
  def implementation(n: Node[?]): Option[Implementation] = byContract.get(n.id)
  /** Its implementation, unless it is a Definition's code an earlier statement on it governs: its files have one
    * owner.
    */
  def ownImplementation(n: Node[?]): Option[Implementation] = implementation(n).filter(i => i.definition.forall(d =>
    nodes.find(c => implementation(c).exists(_.definition.contains(d))).forall(_ eq n)))
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
  /** With the examples written as tests: each a case of every claim on its Definition, read by `check`. */
  def withWritten(ws: List[Written]): KnowledgeBase =
    KnowledgeBase(name, idea, implementations, generators, testing, onViolation, ws)(nodes*)
  /** Its cases: its own (`.examples`), and those written as tests of its operation. */
  def casesOf(n: Node[?]): List[Example] =
    n.cases ++ (if n.post.isEmpty then Nil else written.filter(w => n.op.exists(_ eq w.op)).map(_.asCase))
  /** Structural problems; a knowledge base with problems is not checked. */
  lazy val problems: List[Problem] = Validation.problems(this)
