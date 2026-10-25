package frflow

import frflow.protocol.{NodeKind, RunCheck}
import java.util.SplittableRandom
import java.util.concurrent.atomic.{AtomicBoolean, AtomicLong, AtomicReference}
import scala.collection.concurrent.TrieMap

// The run-time path: the user's production code calls `service`'s plain function of the operation's inputs, and the
// predicates it checks read parameters as `param.value` deep inside the user's own code. That path has no
// effect type, and three things here follow from it:
// - The values in force are a ThreadLocal (`Bindings`): there is no argument to pass them through.
// - A broken contract or assumption is reported (`Violation`, to the knowledge base's reporter: a log line by
//   default), then thrown as the documented `ContractViolation`, so that a result that breaks it is never
//   returned (fail closed); a wiring mistake (no implementation, an unbound parameter) is an
//   `IllegalStateException` when the service is wired, not on the first call.
// - Which calls are checked is the contract's `RunCheck`: every call for code Lean does not prove, none for
//   code it proves, or a sample, as the developer decides.
// - A running service remembers, in an atomic reference to an immutable map, what each assumption was last
//   found to hold of; a call reads each parameter once, through a `Cell`.

/** What broke where the code runs: the contract, which check (`its check`, `the contract`, `the invariant I`, `the
  * assumption A`), the call's inputs, and the result (none when the values it runs with break an assumption).
  */
final case class Violation(contract: String, check: String, inputs: List[Any], result: Option[Any]):
  private def args = inputs.map(Example.show).mkString("(", ", ", ")")
  def message: String = result match
    case Some(r)                => s"$contract: result ${Example.show(r)} for $args breaks $check"
    case None if inputs.isEmpty => s"$contract: the values it starts with break $check"
    case None                   => s"$contract: the values it runs with break $check"
  /** One line with named fields, for logs to search and alert on. */
  def line: String =
    s"frflow contract violation: contract=$contract check=\"$check\" inputs=$args" + result.fold("")(r => s" result=${Example.show(r)}")

object Violation:
  /** The default report: the line, at ERROR, to the platform's logger named `frflow`. */
  val log: Violation => Unit = v => System.getLogger("frflow").log(System.Logger.Level.ERROR, v.line)

/** Raised where a result or a value breaks what was decided, after the violation is reported: the result is never
  * returned (fail closed). An application maps it to its own failure (an HTTP layer, to a 500).
  */
final class ContractViolation(val violation: Violation) extends RuntimeException(violation.message)

object Bindings:
  /** What is bound where code runs: a scope's own bindings, then those of the scope it is in. Entering one costs
    * nothing for what is bound around it, so a call of a service in a large knowledge base stays cheap.
    */
  private[frflow] abstract class Scope(val outer: Scope | Null):
    def own(name: String): (() => Any) | Null
    final def find(name: String): (() => Any) | Null =
      var s = this: Scope | Null
      var v: (() => Any) | Null = null
      while v == null && s != null do
        v = s.own(name)
        s = s.outer
      v
  private final class Given(bound: Map[String, () => Any], outer: Scope | Null) extends Scope(outer):
    def own(name: String): (() => Any) | Null = bound.getOrElse(name, null)

  /** One call's values (`service`): each binding read when first needed, then the same for the rest of the call. */
  private[frflow] final class Call(index: Map[String, Int], bindings: IndexedSeq[Binding], outer: Scope | Null) extends Scope(outer):
    private val cells = new Array[Cell | Null](bindings.size)
    private def cell(i: Int): Cell = cells(i) match
      case null => val c = Cell(bindings(i)); cells(i) = c; c
      case c: Cell => c
    def own(name: String): (() => Any) | Null = index.get(name).fold(null)(i => () => cell(i).get)
    def loaded(name: String): Boolean = index.get(name).exists(i => cells(i) != null && cells(i).nn.loaded)
    def value(name: String): Option[Any] = index.get(name).map(cell(_).get)

  /** A call's scope over the scope in force, for `bindings` indexed once by name (the last of a name wins). */
  private[frflow] def call(index: Map[String, Int], bindings: IndexedSeq[Binding]): Call = Call(index, bindings, current.get)
  private[frflow] def index(bindings: Seq[Binding]): Map[String, Int] = bindings.iterator.map(_.param.name).zipWithIndex.toMap

  private val current = ThreadLocal.withInitial[Scope](() => Given(Map.empty, null))
  private val reads = ThreadLocal[scala.collection.mutable.Set[String] | Null]()
  def get[A](p: Param[A]): A =
    if Building.active then
      throw IllegalStateException(s"FrFlow: ${p.name}.value is read while a model is built, so the value it has now would be " +
        s"fixed into its Lean and its running code: use ${p.name} itself as a term")
    val value = current.get.find(p.name) match
      case null => throw IllegalStateException(s"parameter ${p.name} is not bound")
      case v: (() => Any) @unchecked => v
    reads.get match
      case null => value().asInstanceOf[A]
      case seen =>
        // What the code reads itself: not what a definition or an operation's code reads in turn.
        seen += p.name
        reads.set(null)
        try value().asInstanceOf[A]
        finally reads.set(seen)

  /** A parameter as a term reads it (a definition's or a contract's formula, run): not a read of the plain code under test. */
  private[frflow] def ofTerm[A](p: Param[A]): A =
    val saved = reads.get
    reads.set(null)
    try get(p)
    finally reads.set(saved)

  /** What `body` returns, and the parameters it read itself: what a test learns of plain code it cannot see into. */
  private[frflow] def reading[T](body: => T): (T, Set[String]) =
    val saved = reads.get
    val seen = scala.collection.mutable.Set.empty[String]
    reads.set(seen)
    try (body, seen.toSet)
    finally reads.set(saved)

  def within[T](bs: Seq[Binding])(body: => T): T =
    in(Given(bs.map(b => b.param.name -> b.value).toMap, current.get))(body)

  /** Bindings named once, to enter many times (each step of a flow's run). */
  private[frflow] final class Prepared(val bound: Map[String, () => Any])
  private[frflow] def prepare(bs: Seq[Binding]): Prepared = Prepared(bs.map(b => b.param.name -> b.value).toMap)
  private[frflow] def within[T](p: Prepared)(body: => T): T = in(Given(p.bound, current.get))(body)

  private[frflow] def in[T](scope: Scope)(body: => T): T =
    val saved = current.get
    current.set(scope)
    try body
    finally current.set(saved)

  /** The bindings, each computed at most once while the bindings in force stay the ones it was computed under: for
    * terms a definition gives (pure, so the same in one world), where the world is fixed (a generated case). Under a
    * scope that binds anything again, it is computed again.
    */
  private[frflow] def oncePerScope(bs: Seq[Binding]): Seq[Binding] = bs.map { b =>
    var scope: AnyRef | Null = null
    var held: Any = null
    b.copy(value = () => {
      val now = current.get
      if !(scope eq now) then
        held = b.value()
        scope = now
      held
    })
  }

/** While a term, a define, a flow or a model's operation is built (once, on symbolic values): a parameter's value read
  * then would become a constant in both its Lean and its Scala, so `Bindings.get` refuses it.
  */
private[frflow] object Building:
  private val depth = ThreadLocal.withInitial[Int](() => 0)
  def apply[T](body: => T): T =
    depth.set(depth.get + 1)
    try body
    finally depth.set(depth.get - 1)
  def active: Boolean = depth.get > 0

final case class Assumption(what: String, reads: Set[String], holds: () => Boolean)

/** The code registered for a contract's operation: `wiring` is its source; `proven`, the `define` Lean proves. */
final case class Implementation(contract: String, factory: () => Any, files: List[String], wiring: String = "", proven: Option[Def[?]] = None,
    flowDef: Option[Def[?]] = None, calls: List[String] = Nil):
  /** Proven code that is a flow: `proven` is its run on the models, `flowDef` the flow itself. */
  def flow: Boolean = flowDef.isDefined
  /** The running code is the proven `define` itself, not code checked against it (`runs`). */
  def provenCode: Boolean = proven.isDefined && wiring.isEmpty
  // The last of `files` is the model's file, where it is attached.
  def sources: List[String] = files.dropRight(1)
  def modelFile: Option[String] = files.lastOption

object Implementation:
  private val Ident = "[A-Za-z_][A-Za-z0-9_]*".r
  /** A flow attached as a contract's code: `impl` takes the flow's inputs as terms and gives its steps. */
  def ofFlow(contract: Node[?], impl: AnyRef, text: String, files: List[String]): Implementation =
    val (ins, r) = Node.flowTypes(contract.op.getOrElse(throw IllegalArgumentException(s"${contract.id} is not a contract")))
    val name = if Ident.matches(text) then text else contract.id.head.toLower.toString + contract.id.tail
    val flow = Def(Lifted.flow(impl, ins, text), r, Some(name), isFlow = true)
    val pair = LeanType.of[Any](Shape.TupleOf(List(r, summon[LeanType[World]])))
    val code = Def(Lifted.runOn(flow, ins, pair, contract.failure.map(_.err)), pair, Some(s"${name}_run"))
    Implementation(contract.id, () => code.lifted.value, files, "", Some(code), Some(flow))

/** Runs a flow's proven code in `G`: `knowledge.run[IO](expiryJob)(db.bind(sqlite))` is the job, a function of its inputs. */
final class Runner[G[_]] private[frflow] (kb: KnowledgeBase)(using G: cats.effect.kernel.Sync[G]):
  def apply[F](contract: Node[F])(using s: Sig[F])(bound: (Binding | Boundary.Bound)*): s.Runs[G] =
    val flow = kb.implementation(contract).flatMap(_.flowDef)
      .getOrElse(throw IllegalStateException(s"no flow implements ${contract.id}: implementProven(${contract.id})(…)"))
    val bindings = bound.collect { case b: Binding => b }
    val impls: Map[Boundary[?], Any] = bound.collect { case b: Boundary.Bound => b.boundary -> b.impl }.toMap
    val (bs, body) = flow.lifted.built
    val steps = body.termTree match
      case Tree.Do(s) => s
      case _          => throw IllegalStateException(s"${flow.name} is not a flow")
    Steps.boundaries(steps).filterNot(impls.contains).foreach(b =>
      throw IllegalStateException(s"${contract.id}: bind the boundary ${b.name} (${b.name}.bind(…))"))
    val bound2 = bindings.map(_.param.name).toSet
    val all = bindings ++ kb.definitionBindings.filterNot(b => bound2(b.param.name)) ++ Wiring.calls(kb, bindings).filterNot(b => bound2(b.param.name))
    Fn.of(bs.size)(args => Flows.run[G](steps, bs.zip(args).toMap, impls, all)).asInstanceOf[s.Runs[G]]

/** A parameter's value for one call, read when first needed; a function it holds answers each question once. */
private[frflow] final class Cell(val binding: Binding):
  private val read = AtomicBoolean(false)
  lazy val get: Any =
    val v = Cell.memoized(binding.value())
    read.set(true)
    v
  def loaded: Boolean = read.get

private[frflow] object Cell:
  private def lambda(f: AnyRef) = f.getClass.getName.contains("Lambda")

  private def memo(f: Any => Any): Any => Any =
    val seen = TrieMap.empty[Any, Any]
    a => seen.getOrElseUpdate(a, f(a))

  def memoized(v: Any): Any = v match
    case f: Function1[?, ?] if lambda(f) => memo(f.asInstanceOf[Any => Any])
    // A function of more arguments answers each list of them once.
    case f: AnyRef if lambda(f) && Fn.arity(f).exists(_ >= 2) =>
      val m = memo(args => Fn.call(f, args.asInstanceOf[List[Any]]))
      Fn.of(Fn.arity(f).get)(m)
    case other => other

// The IR is untyped: the builders gave the post, the check and the views the types of a call of the operation, so here a
// call is its inputs (a flow's run: its inputs and the world before) and its result (a flow's: the result and the world after).
extension (n: Node[?])
  private[frflow] def postFn: Option[(List[Any], Any) => Boolean] = n.post.map { p =>
    if n.isFlow then (ins: List[Any], r: Any) => r match
      // A run that failed: what the contract says of one (nothing changed, or its failure clause).
      case (Failed(e), after) => n.failure.exists(f => f.post.fold(after == ins.last)(fp =>
        Fn.call(fp.value, List(e, ins.last, after)).asInstanceOf[Boolean]))
      case (x, after) => Fn.call(p.value, ins.init ++ List(x, ins.last, after)).asInstanceOf[Boolean]
      case _          => false
    else (ins: List[Any], r: Any) => Fn.call(p.value, ins :+ r).asInstanceOf[Boolean]
  }
  def broken(inputs: List[Any], r: Any): Option[String] = n.kept.find(_.brokenBy(inputs, r)).map(_.invariant.id)

extension [F](n: Node[F])
  /** `impl` (a Scala function of the operation's inputs) wrapped as `service` runs it: a function of the same inputs. */
  private[frflow] def enforce(impl: F, assumes: List[Assumption] = Nil, runCheck: RunCheck = RunCheck.EveryCall,
      report: Violation => Unit = Violation.log)(bindings: Binding*): F =
    // The cheap check when the contract gives one (Lean proves the post implies it), else the post.
    val (lifted, what) = (n.local, n.post) match
      case (Some(l), Some(_)) => (l, "its check")
      case (None, Some(p))    => (p, "the contract")
      case _                  => throw IllegalArgumentException(s"${n.id} is not a contract")
    val check = lifted.value
    val sampled = RunTimeChecks.chooser(runCheck)
    // What each assumption was last found to hold of: checked again when a value it reads changes.
    val held = AtomicReference(Map.empty[String, List[Any]])
    def same(xs: List[Any], ys: List[Any]) =
      xs.size == ys.size && xs.zip(ys).forall((p, q) => p.asInstanceOf[AnyRef] eq q.asInstanceOf[AnyRef])
    def fail(v: Violation): Nothing = { report(v); throw ContractViolation(v) }
    val all = bindings.toIndexedSeq
    val index = Bindings.index(all)
    Fn.of(n.op.map(Node.arity).getOrElse(0)) { ins =>
      // Each parameter is read once per call, and only if something reads it (a whole table a cheap check does
      // not read is never loaded): the implementation and the check see the same values.
      val cells = Bindings.call(index, all)
      Bindings.in(cells) {
        val r = Fn.call(impl.asInstanceOf[AnyRef], ins)
        if sampled() then
          if !Fn.call(check, ins :+ r).asInstanceOf[Boolean] then fail(Violation(n.id, what, ins, Some(r)))
          n.broken(ins, r).foreach(i => fail(Violation(n.id, s"the invariant $i", ins, Some(r))))
        // The values it ran with are checked whatever the code: they are about the world, and cheap (once per change).
        assumes.filter(x => x.reads.forall(cells.loaded)).foreach { x =>
          val vs = x.reads.toList.sorted.flatMap(cells.value)
          if !held.get.get(x.what).exists(same(_, vs)) then
            if !x.holds() then fail(Violation(n.id, s"the assumption ${x.what}", ins, None))
            held.updateAndGet(_.updated(x.what, vs))
        }
        r
      }
    }.asInstanceOf[F]

/** Which calls a run-time check checks. */
private[frflow] object RunTimeChecks:
  def chooser(c: RunCheck): () => Boolean = c match
    case RunCheck.EveryCall => () => true
    case RunCheck.Never     => () => false
    case RunCheck.Sampled(k, None) =>
      val calls = AtomicLong(0)
      () => calls.getAndIncrement() % k == 0
    case RunCheck.Sampled(k, Some(seed)) =>
      val random = SplittableRandom(seed)
      () => random.synchronized(random.nextInt(k) == 0)

/** Wiring a knowledge base's code into a running system (see `KnowledgeBase.service`). */
private[frflow] object Wiring:
  def service[F](kb: KnowledgeBase, contract: Node[F], bindings: Seq[Binding]): F =
    val i = kb.implementation(contract).getOrElse(throw IllegalStateException(s"no implementation of ${contract.id}"))
    val bound = bindings.map(_.param.name).toSet
    val defined = kb.definitionBindings.filterNot(b => bound(b.param.name))
    val calls = Wiring.calls(kb, bindings).filterNot(b => bound(b.param.name) || contract.op.exists(_ eq b.param))
    // Fail when wired, not on the first call: every parameter the contract or its examples read must be bound
    // (a contract that starts reading a new parameter breaks old wiring here).
    val auto = (defined ++ calls).map(_.param.name).toSet
    val needed = (contract.post.toList.flatMap(kb.reads) ++ contract.cases.flatMap(_.bindings.map(_.param.name))).distinct
      .filterNot(p => auto(p) || contract.op.exists(_.name == p))
    val missing = needed.filterNot(bound)
    if missing.nonEmpty then throw IllegalStateException(s"${contract.id}: bind ${missing.mkString(", ")} (the contract reads them)")
    val all = bindings ++ defined ++ calls
    val assumes = kb.runtimeAssumptions.filter(_.reads.subsetOf(bound))
    Bindings.within(all)(assumes.find(!_.holds())).foreach { x =>
      val v = Violation(contract.id, s"the assumption ${x.what}", Nil, None)
      kb.onViolation(v)
      throw ContractViolation(v)
    }
    val runTime = kb.runTime(contract).map(_.check).getOrElse(RunCheck.EveryCall)
    // The code is built on each call, under the values in force then.
    val code = Fn.of(contract.op.map(Node.arity).getOrElse(0))(ins => Fn.call(i.factory(), ins)).asInstanceOf[F]
    contract.enforce(code, assumes, runTime, kb.onViolation)(all*)

  /** Each operation some contract's code implements, bound to its service (made when first called). */
  def calls(kb: KnowledgeBase, bindings: Seq[Binding]): List[Binding] =
    opBindings(kb) { (c, _) =>
      lazy val s: AnyRef = service(kb, c.asInstanceOf[Node[AnyRef]], bindings)
      val g = Fn.of(c.op.map(Node.arity).getOrElse(0))(ins => Fn.call(s, ins))
      () => g
    }

  def definitionBindings(kb: KnowledgeBase): List[Binding] =
    kb.provisional.toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t))
      .flatMap(s => s.param.zip(s.term).map((p, l) => Binding(p, () => l.value)))
  def opCode(kb: KnowledgeBase): List[Binding] = opBindings(kb)((_, i) => () => i.factory())

  /** By the code of the first contract on each operation that has some. */
  private def opBindings(kb: KnowledgeBase)(bind: (Node[?], Implementation) => () => Any): List[Binding] =
    kb.onOp.toList.sortBy(_._1).flatMap { (_, ns) =>
      (for c <- ns; op <- c.op; i <- kb.implementation(c) yield Binding(op, bind(c, i))).take(1)
    }

  /** The assumptions of facts, to check where code runs; one over a quantifier cannot be computed: it is trusted only. */
  def runtimeAssumptions(kb: KnowledgeBase): List[Assumption] =
    kb.nodes.filter(_.kind == NodeKind.Assumption).flatMap { n =>
      n.formula.map { l =>
        val f = l.value.asInstanceOf[() => Boolean]
        Assumption(n.id, kb.reads(l).toSet, () => try f() catch case _: NotExecutable => true)
      }
    }
