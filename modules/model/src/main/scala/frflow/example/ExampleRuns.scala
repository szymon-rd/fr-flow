package frflow
package example

import frflow.flow.Flows
import frflow.testing.ModelTests
import scala.util.Try

/** Running a knowledge base's examples, and its code beyond them. */
private[frflow] object ExampleRuns:
  def results(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    // An example need not bind the operations its code calls, nor the defined terms: they run as in service.
    if n.cases.isEmpty then Nil
    else Bindings.within(kb.opCode ++ kb.definitionBindings) {
      n.checkExamples(kb.implementation(n).map(_.factory), kb.runtimeAssumptions) ++
        onReal(kb, n) ++ faultSweep(kb, n) ++ interleavings(kb, n)
    }

  /** How many times each example of a flow with branches at once is run on fibers. */
  val InterleavedRuns: Int = 8

  /** A flow that runs branches at once, run from each of its examples (with no faults) on the boundaries'
    * implementations in IO: the branches on fibers, a random pause before each call of a boundary, so that each run
    * interleaves their steps differently. Each run must give what the proven reading gives on the models (the branches
    * one after the other); a race, whose winner is the scheduler's, must give what the contract allows. A flow whose
    * branches share state outside a transaction is caught here (a lost update), not by the commutation proof, which
    * compares whole branches.
    */
  private def interleavings(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    import cats.effect.IO
    import cats.effect.unsafe.implicits.global
    import scala.concurrent.duration.*
    (for
      flow <- kb.implementation(n).flatMap(_.flowDef).toList
      (bs, body) = flow.lifted.built
      steps <- (body.termTree match { case Tree.Do(s) => Some(s); case _ => None }).toList
      if Steps.parallel(steps)
      post <- n.postFn.toList
      e <- n.cases.filter(c => c.expected && c.inputs.lastOption.exists { case w: World => w.faults.isEmpty; case _ => false })
      used = kb.models.filter(m => Steps.boundaries(steps).contains(m.boundary)).flatMap(m => m.impls.sortBy(_.outside).headOption.map(m -> _))
    yield
      val (args, before) = (e.inputs.init, e.inputs.last.asInstanceOf[World])
      val env = bs.zip(args).toMap
      val name = if used.isEmpty then "no implementation" else used.map((_, i) => ModelTests.implName(i)).mkString(" and ")
      def held(w: World): World = used.foldLeft(w)((acc, x) => acc.updated(x._1.model, x._2.read(x._2.start(acc(x._1.model.asInstanceOf[StateModel[Any]])))))
      val model = Bindings.within(e.bindings)(Try(
        try Flows.onModels(steps, env, held(before)) catch case Flows.Raised(err, at) => (Failed(err), at)).map((r, w) => (r, held(w))))
      val bindings = kb.opCode ++ kb.definitionBindings ++ e.bindings
      val runs = (1 to InterleavedRuns).toList.map { i =>
        val rnd = java.util.SplittableRandom(i * 7919L)
        val pause = IO(rnd.synchronized(rnd.nextInt(300))).flatMap(us => IO.sleep(us.micros))
        Try {
          val started = used.map((o, oi) => (o, oi, oi.start(before(o.model.asInstanceOf[StateModel[Any]]))))
          val impls: Map[Boundary[?], Any] = started.map((o, _, i) => o.boundary -> i).toMap
          val r = Flows.run[IO](steps, env, impls, bindings, Some(pause)).attempt.unsafeRunSync() match
            case Right(v)             => v
            case Left(FlowFailed(err)) => Failed(err)
            case Left(other)          => throw other
          (r, started.foldLeft(before)((w, x) => w.updated(x._1.model, x._2.read(x._3))))
        }
      }
      val racing = Steps.racing(steps)
      val verdict = runs.zipWithIndex.collectFirst(Function.unlift { case (run, i) =>
        (model, run) match
          case (_, scala.util.Failure(x)) => Some(s"run ${i + 1} on $name: error ${x.getMessage}")
          case (scala.util.Failure(x), _) => Some(s"error on the models: ${x.getMessage}")
          case (scala.util.Success(m), scala.util.Success(y)) =>
            if racing then Option.when(!Bindings.within(e.bindings)(Try(post(args :+ before, y)).getOrElse(false)))(
              s"run ${i + 1} on $name gives ${Example.show(y)}, which the contract forbids")
            else Option.when(m != y)(s"run ${i + 1} on $name, its branches interleaved, gives ${Example.show(y)}, where the models (the branches in turn) give ${Example.show(m)}")
      }).getOrElse("ok")
      ExampleResult(e.copy(note = s"${e.note}, its branches at once ($InterleavedRuns runs on fibers, interleaved, on $name)"), "ok", Some(verdict))
    )

  /** A flow that may fail, run from each of its examples with one call of its failing boundaries failing, each in turn
    * (the first, the second, …, until the run makes no more): on the models and on the boundaries' implementations,
    * with the same fault injected. Each run must meet the contract (its failure clause, for one that fails), and give
    * on the implementations what it gives on the models.
    */
  private def faultSweep(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    (for
      flow <- kb.implementation(n).flatMap(_.flowDef).toList if n.failure.isDefined
      (bs, body) = flow.lifted.built
      steps <- (body.termTree match { case Tree.Do(s) => Some(s); case _ => None }).toList
      if Steps.boundaries(steps).exists(_.fails) && !Steps.racing(steps)
      post <- n.postFn.toList
      e <- n.cases.filter(c => c.expected && c.inputs.lastOption.exists { case w: World => w.faults.isEmpty; case _ => false })
      used = kb.models.filter(m => Steps.boundaries(steps).contains(m.boundary)).flatMap(m => m.impls.sortBy(_.outside).headOption.map(m -> _))
      k <- 1 to 12
      before = e.inputs.last.asInstanceOf[World].failing((List.fill(k - 1)(false) :+ true)*)
      args = e.inputs.init
      model = Bindings.within(e.bindings)(Try(
        try Flows.onModels(steps, bs.zip(args).toMap, before) catch case Flows.Raised(err, at) => (Failed(err), at)))
      // Past the run's last call of a failing boundary, the fault is never taken: the sweep ends there.
      if model.toOption.exists { case (Failed(_), at: World) => at.faults.isEmpty; case _ => false }
    yield
      val name = used.map((_, i) => ModelTests.implName(i)).mkString(" and ")
      val onContract = model match
        case scala.util.Success(r @ (Failed(err), w)) =>
          if post(args :+ before, r) then "ok" else s"the run fails with ${Example.show(err)} and leaves $w, which the contract forbids"
        case scala.util.Success(r) => if post(args :+ before, r) then "ok" else s"the run gives ${Example.show(r)}, which the contract forbids"
        case scala.util.Failure(x) => s"error on the models: ${x.getMessage}"
      def held(w: World): World = used.foldLeft(w)((acc, x) => acc.updated(x._1.model, x._2.read(x._2.start(acc(x._1.model.asInstanceOf[StateModel[Any]])))))
      val real = Bindings.within(e.bindings)(Try {
        val started = used.map((o, oi) => (o, oi, oi.start(before(o.model.asInstanceOf[StateModel[Any]]))))
        val impls = FaultPlan(before.faults).all(started.map((o, _, i) => o.boundary -> i).toMap)
        val r = try Flows.runNow(steps, bs.zip(args).toMap, impls) catch case FlowFailed(err) => Failed(err)
        (r, started.foldLeft(before)((w, x) => w.updated(x._1.model, x._2.read(x._3))))
      })
      val onCode = (model.map((r, w) => (r, held(w))), real) match
        case (scala.util.Success(x), scala.util.Success(y)) if x == y => "ok"
        case (scala.util.Success(x), scala.util.Success(y)) => s"on $name gives ${Example.show(y)}, where the model gives ${Example.show(x)}"
        case (_, scala.util.Failure(x)) => s"error on $name: ${x.getMessage}"
        case (scala.util.Failure(x), _) => s"error on the models: ${x.getMessage}"
      ExampleResult(e.copy(note = s"${e.note}, its call $k of a failing boundary failing (run on $name)"), onContract, Some(onCode))
    )

  /** A flow's examples run on each implementation of its boundaries (an outside system, or the project's own), started in
    * each model's state before: what they give, read back, must be what the run on the models gives. Both are compared
    * as the implementation holds a state: the model runs from the example's state stored and read back, and its state
    * after is stored in a fresh implementation and read back. What the implementation does not keep (the order of rows a
    * table returns sorted) is then not compared; what it keeps (the order of an event log) is.
    */
  private def onReal(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    (for
      flow <- kb.implementation(n).flatMap(_.flowDef).toList
      (bs, body) = flow.lifted.built
      steps <- (body.termTree match { case Tree.Do(s) => Some(s); case _ => None }).toList
      if !Steps.racing(steps)
      mo <- kb.models.filter(m => Steps.boundaries(steps).contains(m.boundary))
      impl <- mo.impls
      e <- n.cases.filter(_.expected)
    yield
      val (args, before) = (e.inputs.init, e.inputs.last.asInstanceOf[World])
      // The flow's other boundaries run on their own first implementation (the project's own, when it has one).
      val others = kb.models.filter(o => (o ne mo) && Steps.boundaries(steps).contains(o.boundary))
        .flatMap(o => o.impls.sortBy(_.outside).headOption.map(o -> _))
      val used = (mo -> impl) :: others
      def held(w: World): World = used.foldLeft(w)((acc, x) => acc.updated(x._1.model, x._2.read(x._2.start(acc(x._1.model.asInstanceOf[StateModel[Any]])))))
      val name = ModelTests.implName(impl)
      // Under the example's own values too: the operations the flow calls read them.
      // A run that fails gives `Failed(error)`: on the models as the world's faults say, on the implementations with the
      // same faults injected into the failing boundaries' calls.
      val model = Bindings.within(e.bindings)(Try(
        try Flows.onModels(steps, bs.zip(args).toMap, held(before)) catch case Flows.Raised(err, at) => (Failed(err), at))
        .map((r, w) => (r, held(w))))
      val real = Bindings.within(e.bindings)(Try {
        val started = used.map((o, oi) => (o, oi, oi.start(before(o.model.asInstanceOf[StateModel[Any]]))))
        val impls = FaultPlan(before.faults).all(started.map((o, _, i) => o.boundary -> i).toMap)
        val r = try Flows.runNow(steps, bs.zip(args).toMap, impls) catch case FlowFailed(err) => Failed(err)
        (r, started.foldLeft(before)((w, x) => w.updated(x._1.model, x._2.read(x._3))))
      })
      val verdict = (model, real) match
        case (scala.util.Success(x), scala.util.Success(y)) if x == y => "ok"
        case (scala.util.Success(x), scala.util.Success(y)) => s"on $name gives ${Example.show(y)}, where the model gives ${Example.show(x)}"
        case (_, scala.util.Failure(x)) => s"error on $name: ${x.getMessage}"
        case (scala.util.Failure(x), _) => s"error on the models: ${x.getMessage}"
      ExampleResult(e.copy(note = s"${e.note} (run on $name)"), "ok", Some(verdict))
    )

  // The examples run the developer's code: what it throws is a finding about that code, said in the verdict
  // ("error: …"), never a failure of the run.
  private[frflow] def verdict(t: Try[String]): String = t.fold(e => s"error: ${e.getMessage}", identity)
