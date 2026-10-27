package frflow

import frflow.protocol.NodeKind
import frflow.testing.Coverage
import frflow.testing.ModelTests
import frflow.testing.Plan
import frflow.testing.Shrink
import frflow.testing.Table
import frflow.types.Shape
import java.util.SplittableRandom
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/** Testing a contract's code against the contract: the property is the contract's own formula, run in Scala on cases
  * generated from the types (the examples' values among them), on the code's result; the formula's parts are counted,
  * so a part no case reaches is reported.
  */
private[frflow] object Testing:
  /** A failing case, shrunk: shown, why it fails, and where it came from (the same seed, index and size make it again). */
  final case class Failed(shown: String, why: String, seed: Long, index: Int, size: Int)
  /** A case to try first: one that failed before. */
  final case class Replay(seed: Long, index: Int, size: Int)
  final case class Covered(part: String, held: Int)
  /** `against`: what the code is tested against (the contract, or the proven define it runs beside). */
  final case class Report(cases: Int, seed: Long, against: String, failure: Option[Failed], coverage: List[Covered], notes: List[String]):
    def passed: Boolean = failure.isEmpty && coverage.forall(_.held > 0)

  /** The code of a contract that is tested, not proven: plain code on its operation, or code run beside a proven define. */
  def testable(kb: FrModel, n: Node[?]): Option[Implementation] =
    kb.implementation(n).filter(i => !i.flow && !i.provenCode && !n.isFlow && n.post.isDefined && n.op.isDefined)

  /** Whether the node has code tested by `run`: a contract's plain code, or implementations of a boundary's model. */
  def tests(kb: FrModel, n: Node[?]): Boolean = testable(kb, n).isDefined || ModelTests.testable(n)

  def run(kb: FrModel, n: Node[?], settings: TestSettings, replay: List[Replay] = Nil): Option[Report] =
    if ModelTests.testable(n) then Some(ModelTests.run(kb, n, settings, replay))
    else testable(kb, n).map(i => Run(kb, n, i).report(settings, replay))

  /** A case the step from `contract` to `claim` fails on, shrunk: the claim's outer `forall` over the contract's inputs,
    * the operation answering as `answer` (a function the contract allows), the claim's other quantifiers sampled as in
    * the tests. Its values: the world the contract reads, then the inputs. None when the claim is not of that shape,
    * or no generated case breaks it.
    */
  def refute(kb: FrModel, contract: Node[?], claim: Node[?], answer: AnyRef, settings: TestSettings): Option[Refuted] =
    for
      formula <- claim.formula
      op <- contract.op
      (bs, body) <- formula.built._2.termTree match
        case Tree.Quant(true, bs, body) => Some((bs, body))
        case _                          => None
      found <- Run(kb, contract, Implementation(contract.id, () => answer, Nil)).refute(bs, body, op, answer, settings)
    yield found

  /** A case a step fails on: its values by name, and what the contract's answer was on it. */
  final case class Refuted(values: List[(String, Any, LeanType[?])], answer: Any)

  /** The types the definitions in force give the opaque terms: what an opaque value is generated as. */
  def opaques(kb: FrModel): Map[String, LeanType[?]] =
    kb.opaques.flatMap(o => kb.provisional.get(o.name).flatMap(_.substs.find(_.name == o.name)).flatMap(_.typeOf).map(o.name -> _)).toMap

  /** The size a case is made at: small first, larger later. */
  def sizeOf(i: Int, cases: Int): Int = 1 + i * 10 / cases.max(1)
  private[frflow] def random(seed: Long, i: Int): SplittableRandom = SplittableRandom(seed * 0x9E3779B97F4A7C15L + i)

  private final class Run(kb: FrModel, n: Node[?], impl: Implementation):
    private val (tins, tr) = n.op.get.termType.shape match
      case Shape.FnOf(as, r) => (as, r)
      case other => throw IllegalArgumentException(s"FrFlow: ${n.id}'s operation is not a function")
    private val post = n.postFn.get
    private val reference = impl.proven.map(d => (d.name, d.lifted.value.asInstanceOf[AnyRef]))
    private val against = reference.fold(n.id)((name, _) => s"the proven define $name, and ${n.id}")

    // The world: what the formula reads (through the definitions in force) and the examples bind, less the operations.
    // (A parameter only plain code reads, a database handle, the model does not know: the examples bind it.)
    private val read = (n.post.toList ++ n.kept.flatMap(k => k.view.toList ++ k.invariant.rule.toList)).flatMap(kb.reads)
    private def defined(p: Param[?]) = kb.provisional.get(p.name).exists(_.substs.exists(s => s.name == p.name && s.term.isDefined))
    private val params =
      (read.flatMap(r => kb.params.find(_.name == r)) ++ kb.casesOf(n).flatMap(_.bindings.map(_.param)))
      .distinctBy(_.name).filterNot(p => kb.isOp(p.name) || defined(p))
    private val (generated, fixedParams) = params.partition(p => known(p.termType))
    private val fixed: List[Binding] =
      fixedParams.flatMap(p => kb.casesOf(n).flatMap(_.bindings).find(_.param.name == p.name))
    private val types: Vector[LeanType[?]] = (generated.map(_.termType) ++ tins).toVector

    private val opaques: Map[String, LeanType[?]] = Testing.opaques(kb)
    private val customs: Map[LeanType[?], Gen[?]] = kb.generators.toMap
    private val plan =
      val keyOf = Plan(Map.empty, Map.empty, Nil, opaques)
      val seeds = mutable.LinkedHashMap.empty[String, Vector[Any]]
      def harvest(t: LeanType[?], v: Any) = Plan.harvest(t, v, opaques, keyOf.key, seeds)
      kb.casesOf(n).foreach { e =>
        Try { tins.zip(e.inputs).foreach(harvest(_, _)); harvest(tr, e.result) }
        generated.flatMap(p => e.bindings.find(_.param.name == p.name).map(b => p -> b)).foreach { (p, b) =>
          Try(Bindings.within(e.bindings)(harvest(p.termType, b.table.fold(b.value())(t => Table(1, t.toList.map((k, v) => (List(k), Some(v))), None)))))
        }
      }
      Plan(customs.map((t, g) => keyOf.key(t) -> g), seeds.toMap,
        Probes.boundaries(kb.casesOf(n)).flatMap(x => List(x - 1, x, x + 1)).distinct,
        opaques, outside = n.kind == NodeKind.Assumption, holds = kb.holds)

    private def known(t: LeanType[?]): Boolean = t.shape match
      case Shape.Unknown | Shape.WorldT | Shape.FlowOf(_) => false
      case Shape.ListOf(a)   => known(a)
      case Shape.OptionOf(a) => known(a)
      case Shape.EitherOf(e, a) => known(e) && known(a)
      case Shape.SetOf(a)    => known(a)
      case Shape.MapOf(k, v) => known(k) && known(v)
      case Shape.TupleOf(as) => as.forall(known)
      case Shape.FnOf(as, r) => as.nonEmpty && as.size <= Table.MaxArity && (as :+ r).forall(known)
      case Shape.Opq(o)      => opaques.contains(o.name)
      case _                 => true

    // The parts of the formula a test must reach: an implication's premise, each side of an or, each branch, each case
    // of a match, and each list or option a `forall`/`exists` ranges over, not empty.
    private val printer = LeanPrinter()
    private val formula = n.post.get.built
    printer.print(formula._1, formula._2.termTree, formula._2.termType)
    private val targets: List[(Tree, Int, String)] =
      Coverage.targets(formula._2.termTree, t => Try(printer.expr(t)).getOrElse("…"))

    /** Counts the parts reached; ranges a quantifier over values made for its types (sampled: said in the report). */
    private final class Counter(draw: () => Draw) extends Watch:
      val hits = new java.util.IdentityHashMap[Tree, mutable.Map[Int, Int]]()
      var sampled = Set.empty[String]
      targets.foreach((t, _, _) => hits.putIfAbsent(t, mutable.Map.empty))
      def hit(t: Tree, outcome: Int): Unit = Option(hits.get(t)).foreach(m => m.update(outcome, m.getOrElse(outcome, 0) + 1))
      def range(ts: List[LeanType[?]]): Option[List[List[Any]]] = Try {
        sampled ++= ts.map(Types.scala)
        val d = draw()
        val each = ts.map(t => (plan.seedsOf(t).take(3) ++ List.fill(5)(d.value(t))).distinct.toList)
        each.foldRight(List(List.empty[Any]))((xs, rows) => for x <- xs; r <- rows yield x :: r)
      }.toOption
      def held(t: Tree, outcome: Int): Int = Option(hits.get(t)).flatMap(_.get(outcome)).getOrElse(0)

    /** A case: its values (the world's, then the call's inputs), what the code returned, and why it fails, if it does. */
    private def attempt(vals: Vector[Any], watch: Option[Watch]): (Option[Any], Option[String]) =
      on(generated.zip(vals).map((p, v) => Binding(p, () => v)), vals.drop(generated.size).toList, watch)

    // The operations the code was seen to call: plain code says which it calls (`implementTested(c, op)`), and is
    // held to it.
    private val calledOps = mutable.Set.empty[String]
    private val named = impl.calls.toSet ++ n.op.map(_.name) ++
      kb.onOp.keySet.filter(o => s"\\b${java.util.regex.Pattern.quote(o)}\\b".r.findFirstIn(impl.wiring).isDefined)

    private def on(world: List[Binding], ins: List[Any], watch: Option[Watch]): (Option[Any], Option[String]) =
      // In one case the world is fixed: a definition's term (a store replayed from a history) is computed once.
      Bindings.within(kb.opCode ++ Bindings.oncePerScope(kb.definitionBindings) ++ fixed ++ world) {
        Try(Bindings.reading(Fn.call(impl.factory(), ins))) match
          case Failure(e) => (None, Some(s"error: ${Option(e.getMessage).getOrElse(e.toString)}"))
          case Success((r, read)) =>
            calledOps ++= read.filter(kb.isOp)
            def onContract = Try(watch.fold(post(ins, r))(Watch.within(_)(post(ins, r)))) match
              case Success(true)  => None
              case Success(false) => Some(s"returned ${Example.show(r)}, which ${n.id} forbids")
              case Failure(e: NotExecutable) => Some(s"${n.id} cannot be run here: ${e.getMessage}")
              case Failure(e)     => Some(s"${n.id} could not be evaluated: ${Option(e.getMessage).getOrElse(e.toString)}")
            val unlike = reference.flatMap((name, f) => Try(Fn.call(f, ins)).toOption.filterNot(same(_, r))
              .map(x => s"returned ${Example.show(r)}, where the proven define $name returns ${Example.show(x)}"))
            (Some(r), unlike.orElse(onContract).orElse(n.broken(ins, r).map(i => s"returned ${Example.show(r)}, which breaks the invariant $i")))
      }

    // A list the outside returns in its own order is the same result in another order.
    private def same(x: Any, y: Any): Boolean = (x, y) match
      case (xs: List[?], ys: List[?]) => xs.size == ys.size && xs.diff(ys).isEmpty
      case _ => x == y

    // Each example as a whole case (its world and its call): a third of the cases start from one, with one value changed,
    // so what holds only when the world's parts agree (a user signed in, then disabled) is reached.
    private val exampleCases: Vector[Vector[Option[Any]]] = kb.casesOf(n).toVector.map { e =>
      generated.map(p => e.bindings.find(_.param.name == p.name).flatMap(b => Try(Bindings.within(e.bindings)(b.value())).toOption)).toVector ++
        e.inputs.map(Some(_))
    }

    private def generate(seed: Long, i: Int, size: Int): Vector[Any] =
      val d = Draw(random(seed, i), size, plan)
      if exampleCases.nonEmpty && d.chance(0.35) then
        val base = exampleCases(d.below(exampleCases.size)).zip(types).map((v, t) => v.getOrElse(d.value(t)))
        val k = d.below(types.size)
        val near =
          if plan.holdsOnly(types(k)) then Nil else Probes.near(base(k), plan.numbers).filter(plan.holds(types(k)))
        if d.chance(0.25) then base
        else base.updated(k, near match
          case Nil  => d.value(types(k))
          case near => if d.chance(0.5) then near(d.below(near.size)) else d.value(types(k)))
      else types.map(d.value)

    // The inputs' names, as the contract's lambda gives them (by position where it gives none).
    private val inputNames: List[String] =
      val binders = Try(n.post.get.built._1).getOrElse(Nil)
      tins.indices.toList.map(i => binders.lift(i).filterNot(_.wildcard).fold(s"input ${i + 1}")(_.hint))

    /** A case: its inputs by name, then the world it ran in; what the code returned is said by why it fails. */
    private def shown(vals: Vector[Any]): String =
      val ins = inputNames.zip(vals.drop(generated.size)).map((name, v) => s"$name = ${Example.show(v)}")
      val world = generated.zip(vals).map((p, v) => s"${p.name} = ${Example.show(v)}")
      (ins, world) match
        case (Nil, Nil) => "no inputs"
        case (_, Nil)   => ins.mkString(", ")
        case (Nil, _)   => s"given ${world.mkString(", ")}"
        case _          => s"${ins.mkString(", ")}, given ${world.mkString(", ")}"

    /** The first generated case on which `body` (the claim's, over `bs`, the contract's inputs) is false, shrunk. */
    def refute(bs: List[Binder], body: Tree, op: Param[?], answer: AnyRef, settings: TestSettings): Option[Refuted] =
      val same = bs.size == tins.size && bs.map(b => Types.walk(b.tpe).lean) == tins.map(t => Types.walk(t).lean)
      Option.when(same)(Eval.compile(body)).flatMap { run =>
        val counter = Counter(() => Draw(random(settings.seed, -1), 3, plan))
        // A quantifier over numbers ranges over the case's own numbers and their neighbours.
        def watching(vals: Vector[Any]): Watch = Watch.overNumbers(vals.toList, counter.range)
        def breaks(vals: Vector[Any]): Boolean =
          val world = generated.zip(vals).map((p, v) => Binding(p, () => v))
          val env = bs.zip(vals.drop(generated.size)).toMap
          Try(Bindings.within(kb.opCode ++ Bindings.oncePerScope(kb.definitionBindings) ++ fixed ++ world :+ Binding(op, () => answer))(
            Watch.within(watching(vals))(!run(env).asInstanceOf[Boolean]))).getOrElse(false)
        @tailrec def smallest(vals: Vector[Any], rounds: Int): Vector[Any] =
          LazyList.from(types.indices).flatMap(i =>
            Shrink.of(types(i), vals(i), opaques, plan.only).filter(plan.holds(types(i))).take(40)
              .map(v => vals.updated(i, v)))
            .take(400).find(breaks) match
            case Some(c) if rounds > 0 => smallest(c, rounds - 1)
            case _                     => vals
        (0 until settings.cases).iterator.flatMap(i => Try(generate(settings.seed, i, sizeOf(i, settings.cases))).toOption)
          .find(breaks).map { vals =>
            val small = smallest(vals, 100)
            val ins = small.drop(generated.size).toList
            val named = generated.zip(small).map((p, v) => (p.name, v, p.termType)) ++ bs.zip(ins).map((b, v) => (b.hint, v, b.tpe))
            Refuted(named, Try(Bindings.within(kb.opCode ++ kb.definitionBindings)(Fn.call(answer, ins))).getOrElse(None))
          }
      }

    @tailrec private def shrink(vals: Vector[Any], why: String, rounds: Int): (Vector[Any], String) =
      val smaller = LazyList.from(types.indices)
        .flatMap(i => Shrink.of(types(i), vals(i), opaques, plan.only).filter(plan.holds(types(i))).take(40)
          .map(v => vals.updated(i, v)))
        .take(400).map(c => c -> attempt(c, None)._2).collectFirst { case (c, Some(w)) => (c, w) }
      smaller match
        case Some((c, w)) if rounds > 0 => shrink(c, w, rounds - 1)
        case _ => (vals, why)

    def report(settings: TestSettings, replay: List[Replay]): Report =
      val counter = Counter(() => Draw(random(settings.seed, -1), 3, plan))
      // The examples first: what they reach counts (what fails of them, their own check says).
      kb.casesOf(n).filter(_.expected).foreach(e => Try(on(e.bindings, e.inputs, Some(counter))))
      // The cases that failed before, then new ones, small to large.
      val order = replay ++ (0 until settings.cases).map(i => Replay(settings.seed, i, sizeOf(i, settings.cases)))
      val failure = order.iterator.flatMap { c =>
        Try(generate(c.seed, c.index, c.size)).toOption.flatMap { vals =>
          attempt(vals, Some(counter))._2.map { why =>
            val (small, w) = shrink(vals, why, 100)
            Failed(shown(small), w, c.seed, c.index, c.size)
          }
        }
      }.nextOption().orElse(Option.when((calledOps.toSet -- named).nonEmpty) {
        val unnamed = (calledOps.toSet -- named).toList.sorted.mkString(", ")
        Failed("", s"its code calls $unnamed, which it does not name: implement(${n.id}, $unnamed)(…), so the model shows what the code rests on",
          settings.seed, -1, 0)
      })
      val coverage = targets.map((t, o, text) => Covered(text, counter.held(t, o))).distinctBy(_.part)
      val notes = List(
        Option.when(counter.sampled.nonEmpty)(s"forall/exists over ${counter.sampled.mkString(", ")}: sampled, not every value"),
        Option.when(fixed.nonEmpty)(s"${fixed.map(_.param.name).mkString(", ")}: the examples' value (no Lean type to generate it from)"),
        Option.when(generated.isEmpty && kb.casesOf(n).isEmpty)(
          "nothing to vary: no examples, and the claim reads no parameter")
      ).flatten ++ customs.toList.map((t, g) => s"${Types.scala(t)}: ${g.describe} " +
        (if plan.only(t) then "(given: what the outside holds, with the examples' values)" else "(given; derived values for a quarter of them)")) ++
        unreached(settings)
      Report(settings.cases, settings.seed, against, failure, coverage, notes)

    /** A given generator's correspondence with the examples: the examples' values it never makes (kept as seeds). */
    private def unreached(settings: TestSettings): List[String] =
      customs.toList.flatMap { (t, g) =>
        val made: Set[Any] = (0 until 200).flatMap(i => Try(g.draw(Draw(random(settings.seed + 7, i), 5, plan))).toOption).toSet
        val missed = plan.seedsOf(t).filterNot(made)
        Option.when(missed.nonEmpty)(s"${Types.scala(t)}: the examples' ${missed.take(3).map(Example.show).mkString(", ")} never come from the given generator (kept as seeds)")
      }
