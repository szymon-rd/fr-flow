package frflow

import frflow.protocol.NodeKind
import java.util.concurrent.atomic.{AtomicBoolean, AtomicReference}
import scala.collection.concurrent.TrieMap

// The run-time path: the user's production code calls `service`'s plain function `(A, B) => R`, and the
// predicates it checks read parameters as `param.value` deep inside the user's own code. That path has no
// effect type, and three things here follow from it:
// - The values in force are a ThreadLocal (`Bindings`): there is no argument to pass them through.
// - A broken contract or assumption is the documented `ContractViolation`, thrown so that a result that
//   breaks it is never returned (fail closed); a wiring mistake (no implementation, an unbound parameter)
//   is an `IllegalStateException` when the service is wired, not on the first call.
// - A running service remembers, in an atomic reference to an immutable map, what each assumption was last
//   found to hold of; a call reads each parameter once, through a `Cell`.

/** Raised by an enforced implementation whose result breaks its contract. */
final class ContractViolation(node: String, detail: String) extends RuntimeException(s"$node: $detail")

object Bindings:
  private val current = ThreadLocal.withInitial[Map[String, () => Any]](() => Map.empty)
  def get[A](p: Param[A]): A =
    current.get.get(p.name).fold(throw IllegalStateException(s"parameter ${p.name} is not bound"))(_().asInstanceOf[A])

  def within[T](bs: Seq[Binding])(body: => T): T =
    val saved = current.get
    current.set(saved ++ bs.map(b => b.param.name -> b.value))
    try body
    finally current.set(saved)

final case class Assumption(what: String, reads: Set[String], holds: () => Boolean)

/** The code registered for a contract's operation: `wiring` is its source; `proven`, the `define` Lean proves. */
final case class Implementation(contract: String, factory: () => Any, files: List[String], wiring: String = "", proven: Option[Def[?]] = None):
  /** The running code is the proven `define` itself, not code checked against it (`runs`). */
  def provenCode: Boolean = proven.isDefined && wiring.isEmpty
  // The last of `files` is the model's file, where it is attached.
  def sources: List[String] = files.dropRight(1)
  def modelFile: Option[String] = files.lastOption

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
    case f: Function2[?, ?, ?] if lambda(f) =>
      val g = f.asInstanceOf[(Any, Any) => Any]
      val m = memo { case (x, y) => g(x, y) }
      (x: Any, y: Any) => m((x, y))
    case f: Function3[?, ?, ?, ?] if lambda(f) =>
      val g = f.asInstanceOf[(Any, Any, Any) => Any]
      val m = memo { case (x, y, z) => g(x, y, z) }
      (x: Any, y: Any, z: Any) => m((x, y, z))
    case other => other

extension [A, B, R](n: Node[(A, B) => R])
  // The IR is untyped; the builders gave the post this type.
  private[frflow] def postFn: Option[(A, B, R) => Boolean] = n.post.map(_.value.asInstanceOf[(A, B, R) => Boolean])
  def broken(a: A, b: B, r: R): Option[String] = n.kept.find(_.brokenBy(a, b, r)).map(_.invariant.id)

  private[frflow] def enforce(impl: (A, B) => R, assumes: List[Assumption] = Nil)(bindings: Binding*): (A, B) => R =
    // The cheap check when the contract gives one (Lean proves the post implies it), else the post.
    val (lifted, what) = (n.local, n.post) match
      case (Some(l), Some(_)) => (l, "its check")
      case (None, Some(p))    => (p, "the contract")
      case _                  => throw IllegalArgumentException(s"${n.id} is not a contract")
    val check = lifted.value.asInstanceOf[(A, B, R) => Boolean]
    // What each assumption was last found to hold of: checked again when a value it reads changes.
    val held = AtomicReference(Map.empty[String, List[Any]])
    def same(xs: List[Any], ys: List[Any]) =
      xs.size == ys.size && xs.zip(ys).forall((p, q) => p.asInstanceOf[AnyRef] eq q.asInstanceOf[AnyRef])
    (a, b) =>
      // Each parameter is read once per call, and only if something reads it (a whole table a cheap check does
      // not read is never loaded): the implementation and the check see the same values.
      val cells = bindings.map(b => b.param.name -> Cell(b)).toMap
      Bindings.within(cells.values.map(c => Binding(c.binding.param, () => c.get)).toSeq) {
        val r = impl(a, b)
        if !check(a, b, r) then throw ContractViolation(n.id, s"result $r for ($a, $b) breaks $what")
        n.broken(a, b, r).foreach(i => throw ContractViolation(n.id, s"result $r for ($a, $b) breaks the invariant $i"))
        assumes.filter(x => x.reads.forall(p => cells.get(p).exists(_.loaded))).foreach { x =>
          val vs = x.reads.toList.sorted.flatMap(cells.get).map(_.get)
          if !held.get.get(x.what).exists(same(_, vs)) then
            if !x.holds() then throw ContractViolation(n.id, s"the values it runs with break the assumption ${x.what}")
            held.updateAndGet(_.updated(x.what, vs))
        }
        r
      }

/** Wiring a knowledge base's code into a running system (see `KnowledgeBase.service`). */
private[frflow] object Wiring:
  def service[A, B, R](kb: KnowledgeBase, contract: Node[(A, B) => R], bindings: Seq[Binding]): (A, B) => R =
    val i = kb.implementation(contract).getOrElse(throw IllegalStateException(s"no implementation of ${contract.id}"))
    val f = i.factory.asInstanceOf[() => (A, B) => R]
    val bound = bindings.map(_.param.name).toSet
    val defined = kb.definitionBindings.filterNot(b => bound(b.param.name))
    val calls = opBindings(kb) { (c, _) =>
      lazy val s = service(kb, c.asInstanceOf[Node[(Any, Any) => Any]], bindings)
      val g = (x: Any, y: Any) => s(x, y)
      () => g
    }.filterNot(b => bound(b.param.name) || contract.op.exists(_ eq b.param))
    // Fail when wired, not on the first call: every parameter the contract or its examples read must be bound
    // (a contract that starts reading a new parameter breaks old wiring here).
    val auto = (defined ++ calls).map(_.param.name).toSet
    val needed = (contract.post.toList.flatMap(kb.reads) ++ contract.cases.flatMap(_.bindings.map(_.param.name))).distinct
      .filterNot(p => auto(p) || contract.op.exists(_.name == p))
    val missing = needed.filterNot(bound)
    if missing.nonEmpty then throw IllegalStateException(s"${contract.id}: bind ${missing.mkString(", ")} (the contract reads them)")
    val all = bindings ++ defined ++ calls
    val assumes = kb.runtimeAssumptions.filter(_.reads.subsetOf(bound))
    Bindings.within(all)(assumes.find(!_.holds()))
      .foreach(x => throw ContractViolation(contract.id, s"the values it starts with break the assumption ${x.what}"))
    contract.enforce((a, b) => f()(a, b), assumes)(all*)

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
