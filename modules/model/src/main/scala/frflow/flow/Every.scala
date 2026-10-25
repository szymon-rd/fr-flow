package frflow
package flow

/** A job run every `period` seconds (`Flow.every(60)(housekeeping)`). Each run is the job's flow, proven like any other;
  * that runs come every period is the scheduler's promise, an assumption the developer decides (a sleep may wake late).
  */
final class Every private[frflow] (val period: BigInt, val job: Flow[Unit]):
  /** One run as the scheduler makes it: the job, then a sleep of the period. */
  def once: Flow[Unit] = job.flatMap(_ => Flow.sleep(period))
  /** A run for each of `ticks`, in turn: the schedule as the proofs see it. Lean reads it as a `for` loop; a claim over
    * any number of runs is proven by induction on the list (`FrFlow.foldl_invariant`).
    */
  def runs[X](ticks: Term[List[X]]): Flow[Unit] = Flow.Each(ticks, (tick: Term[X]) => once)

  /** The scheduler, in `G`: `run` (the job's proven code, `knowledge.run[G](contract)(…)`), then a sleep of the period on
    * `clock`; `times` runs, or forever. Each run's start time goes to `started`, where the scheduler's assumption can be
    * checked: no gap between two starts longer than the period and what the job takes.
    */
  def schedule[G[_]](clock: Clock, times: Option[Int] = None, started: BigInt => Unit = _ => ())(run: () => G[Unit])(
      using G: cats.effect.kernel.Sync[G]): G[Unit] =
    import cats.syntax.all.*
    def step[A](f: Flow[A]): G[A] = Flows.run[G](Steps.of(f)._1, Map.empty, Map.empty, Nil).map(_.asInstanceOf[A])
    // Each run built when the one before has ended: forever is a loop, not a value built up front.
    def loop(left: Option[Int]): G[Unit] =
      if left.exists(_ <= 0) then G.unit
      else
        for
          t <- step(clock.now)
          _ <- G.delay(started(t))
          _ <- run()
          _ <- step(clock.sleep(Term.lit(period)))
          _ <- loop(left.map(_ - 1))
        yield ()
    loop(times)
