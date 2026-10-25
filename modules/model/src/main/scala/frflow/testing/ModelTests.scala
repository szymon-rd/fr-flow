package frflow
package testing

import frflow.flow.Flows
import java.lang.reflect.Method
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/** Testing an implementation of a boundary against the boundary's model: runs of its operations, generated with their
  * arguments from a generated state, on the implementation and on the model; every result must be the model's, and
  * what the implementation then holds, read back, what the model holds. The project's own code is tested so; an outside
  * system (a database) is checked so, on fewer runs, and its model stays assumed. A failing run is shrunk: fewer
  * operations, smaller arguments, a smaller state.
  */
private[frflow] object ModelTests:
  import Testing.{Covered, Failed, Replay, Report}

  def testable(n: Node[?]): Boolean = n.modelOf.exists(_.impls.nonEmpty)

  /** An outside system is checked on at most this many runs: each run starts it afresh. */
  val OutsideRuns: Int = 200

  /** How an implementation is named in reports: the class its `start` makes, as written (`SqliteDatabase.holding(t)`). */
  def implName(i: ModelImpl): String =
    """[A-Z]\w*""".r.findFirstIn(i.source.replaceFirst("""^[^=]*=>""", "")).getOrElse("its implementation")

  /** An operation of the boundary, built once on symbolic arguments as the model runs it. */
  private final case class Op(method: Method, binders: List[Binder], steps: Steps):
    def name: String = method.getName
    def types: List[LeanType[?]] = binders.map(_.tpe)
  private final case class Call(op: Op, args: List[Any]):
    def shown: String = s"${op.name}${if args.isEmpty then "" else args.map(Example.show).mkString("(", ", ", ")")}"
  /** A generated run: the state it starts from, and its calls. */
  private final case class Run(start: Any, calls: List[Call])

  def run(kb: KnowledgeBase, n: Node[?], settings: TestSettings, replay: List[Replay]): Report =
    val mo = n.modelOf.get
    val model = mo.model
    val ops = mo.boundary.operations.map { m =>
      val bs = m.getParameters.toList.zip(m.getGenericParameterTypes.toList).map((p, t) => Binder(p.getName, LeanType.ofJava(t)))
      Op(m, bs, Building(Steps.of(m.invoke(model, bs.map(_.term[Any])*).asInstanceOf[Flow[?]])._1))
    }
    val opaques = Testing.opaques(kb)
    val seeds = mutable.LinkedHashMap.empty[String, Vector[Any]]
    val keyOf = Plan(Map.empty, Map.empty, Nil, opaques)
    val states = worlds(kb, mo).map(_(model.asInstanceOf[StateModel[Any]]))
    states.foreach(s => Try(Plan.harvest(model.stateType, s, opaques, keyOf.key, seeds)))
    val numbers = states.flatMap(Probes.numbers).distinct.flatMap(x => List(x - 1, x, x + 1)).distinct
    def plan(outside: Boolean) = Plan(kb.generators.toMap.map((t, g) => keyOf.key(t) -> g), seeds.toMap, numbers, opaques, outside)

    // The parts to reach: each operation called, and each branch of the model's operations.
    val printer = LeanPrinter()
    val targets: List[(Op, Tree, Int, String)] =
      ops.flatMap(o => Coverage.targets(o.steps, t => Try(printer.expr(t)).getOrElse("…")).map((t, k, text) => (o, t, k, s"${o.name}: $text")))
    val counter = Counter()

    val results = mo.impls.map { impl =>
      val p = plan(impl.outside)
      val runs = if impl.outside then settings.cases.min(OutsideRuns) else settings.cases
      Tester(impl, model, ops, p, opaques, counter).test(settings.seed, runs, replay) -> runs
    }
    val failure = results.collectFirst { case (Some(f), _) => f }
    val coverage = ops.map(o => Covered(s"${o.name} called", counter.calls.getOrElse(o.name, 0))) ++
      targets.map((_, t, k, text) => Covered(text, counter.held(t, k))).distinctBy(_.part)
    val notes = mo.impls.zip(results).map { case (impl, (_, runs)) =>
      val kind = if impl.outside then "an outside system: its model is assumed; these runs check it" else "the project's own code, tested"
      s"${implName(impl)} ($kind): $runs runs of 1 to 12 operations each, from generated states"
    } ++ kb.generators.map((t, g) => s"${Types.scala(t)}: ${g.describe} (given)")
    Report(results.map(_._2).sum, settings.seed, s"the model ${model.lean}", failure, coverage, notes)

  /** The states the examples of the flows calling the boundary start from and end in: seeds of the generated ones. */
  private def worlds(kb: KnowledgeBase, mo: ModelOf): List[World] =
    kb.nodes.filter(_.isFlow).flatMap(_.cases).flatMap { e =>
      e.inputs.lastOption.toList ++ (e.result match { case (_, w) => List(w); case _ => Nil })
    }.collect { case w: World if w.parts.contains(mo.model) => w }

  /** What a test saw of the model: the operations called, and how often each branch went each way. */
  private final class Counter extends Watch:
    val calls = mutable.Map.empty[String, Int]
    private val hits = new java.util.IdentityHashMap[Tree, mutable.Map[Int, Int]]()
    def hit(t: Tree, outcome: Int): Unit =
      val m = Option(hits.get(t)).getOrElse { val x = mutable.Map.empty[Int, Int]; hits.put(t, x); x }
      m.update(outcome, m.getOrElse(outcome, 0) + 1)
    def range(types: List[LeanType[?]]): Option[List[List[Any]]] = None
    def held(t: Tree, outcome: Int): Int = Option(hits.get(t)).flatMap(_.get(outcome)).getOrElse(0)

  private final class Tester(impl: ModelImpl, model: StateModel[?], ops: List[Op], plan: Plan, opaques: Map[String, LeanType[?]],
      counter: Counter):
    private val name = implName(impl)
    private val stateType = model.stateType
    private def held(s: Any): Any = impl.read(impl.start(s))

    private def generate(seed: Long, index: Int, size: Int): Run =
      val d = Draw(Testing.random(seed, index), size, plan)
      val start = d.value(stateType)
      Run(start, List.fill(1 + d.below(size + 2))(ops(d.below(ops.size))).map(o => Call(o, o.types.map(d.value))))

    /** Where a run first differs from the model, and how; `watch`, to count what it reaches. */
    private def attempt(r: Run, watch: Boolean): Option[(Int, String)] =
      Try {
        val real = impl.start(r.start)
        r.calls.zipWithIndex.foldLeft((held(r.start), Option.empty[(Int, String)])) { case ((st, found), (c, k)) =>
          if found.isDefined then (st, found)
          else
            if watch then counter.calls.update(c.op.name, counter.calls.getOrElse(c.op.name, 0) + 1)
            val env = c.op.binders.zip(c.args).toMap
            val (expected, next) =
              if watch then Watch.within(counter)(Flows.onModel(c.op.steps, model, st, env)) else Flows.onModel(c.op.steps, model, st, env)
            Try(Flows.runNow(Steps.of(c.op.method.invoke(real, c.args.map(Flows.literal)*).asInstanceOf[Flow[?]])._1, Map.empty, Map.empty)) match
              case Failure(e) => (st, Some(k -> s"${c.shown} failed on $name: ${message(e)}"))
              case Success(got) if got != expected =>
                (st, Some(k -> s"${c.shown} returned ${Example.show(got)} on $name, where the model returns ${Example.show(expected)}"))
              case Success(_) =>
                val (want, now) = (held(next), impl.read(real))
                if want != now then (st, Some(k -> s"after ${c.shown}, $name holds ${Example.show(now)}, where the model holds ${Example.show(want)}"))
                else (want, None)
        }._2
      } match
        case Success(r) => r
        case Failure(e) => Some(0 -> s"error on $name: ${message(e)}")

    private def message(e: Throwable): String = e match
      case x: java.lang.reflect.InvocationTargetException if x.getCause != null => message(x.getCause)
      case x => Option(x.getMessage).getOrElse(x.toString)

    /** Smaller runs: fewer calls, smaller arguments, a smaller state (but values only a given generator makes). */
    private def smaller(r: Run): LazyList[Run] =
      def shrinks(t: LeanType[?], v: Any) = Shrink.of(t, v, opaques, plan.only)
      val fewer = LazyList.from(r.calls.indices).map(i => r.copy(calls = r.calls.patch(i, Nil, 1))).filter(_.calls.nonEmpty)
      val args = LazyList.from(r.calls.indices).flatMap { i =>
        val c = r.calls(i)
        LazyList.from(c.args.indices).flatMap(j => shrinks(c.op.types(j), c.args(j)).take(8)
          .map(v => r.copy(calls = r.calls.updated(i, c.copy(args = c.args.updated(j, v))))))
      }
      val state = shrinks(stateType, r.start).take(20).map(s => r.copy(start = s))
      fewer ++ args ++ state

    @tailrec private def shrink(r: Run, at: (Int, String), rounds: Int): (Run, (Int, String)) =
      smaller(r).take(300).map(c => c -> attempt(c, watch = false)).collectFirst { case (c, Some(w)) => (c, w) } match
        case Some((c, w)) if rounds > 0 => shrink(c, w, rounds - 1)
        case _ => (r, at)

    def test(seed: Long, runs: Int, replay: List[Replay]): Option[Failed] =
      val order = replay ++ (0 until runs).map(i => Replay(seed, i, Testing.sizeOf(i, runs)))
      order.iterator.flatMap { c =>
        Try(generate(c.seed, c.index, c.size)).toOption.flatMap { r =>
          attempt(r, watch = true).map { found =>
            val (small, (k, why)) = shrink(r, found, 100)
            val shown = s"on $name, from ${Example.show(small.start)}: ${small.calls.take(k + 1).map(_.shown).mkString("; ")}"
            Failed(shown, why, c.seed, c.index, c.size)
          }
        }
      }.nextOption()
