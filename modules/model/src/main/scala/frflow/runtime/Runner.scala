package frflow
package runtime

import frflow.flow.Flows

/** Runs a flow's proven code in `G`: `knowledge.run[IO](expiryJob)(db.bind(sqlite))` is the job, a function of its inputs. */
final class Runner[G[_]] private[frflow] (kb: FrModel)(using G: cats.effect.kernel.Sync[G]):
  /** The proven flow of a Definition: `knowledge.run[IO](book)(store.bind(sqlite))`. */
  def apply[F](d: Definition[F])(using s: Sig[F])(bound: (Binding | Boundary.Bound)*): s.Runs[G] =
    val contract = kb.claimsOn(d).find(c => kb.implementation(c).exists(_.flowDef.isDefined))
      .getOrElse(throw IllegalStateException(s"no flow gives ${d.name} its meaning: implementProven(${d.name})(…)"))
    apply(contract.asInstanceOf[Node[F]])(bound*)

  def apply[F](contract: Node[F])(using s: Sig[F])(bound: (Binding | Boundary.Bound)*): s.Runs[G] =
    val flow = kb.implementation(contract).flatMap(_.flowDef)
      .getOrElse(throw IllegalStateException(s"no flow implements ${contract.id}: implementProven(${contract.id})(…)"))
    val bindings = bound.collect { case b: Binding => b }
    val impls: Map[Boundary[?], Any] = bound.collect { case b: Boundary.Bound => b.boundary -> b.impl }.toMap
    val (bs, body) = flow.lifted.built
    val steps = body.termTree match
      case Tree.Do(s) => s
      case _          => throw IllegalStateException(s"${flow.name} is not a flow")
    Steps.boundaries(steps).filterNot(b => impls.contains(b) || (b eq Races.boundary)).foreach(b =>
      throw IllegalStateException(s"${contract.id}: bind the boundary ${b.name} (${b.name}.bind(…))"))
    val bound2 = bindings.map(_.param.name).toSet
    val all = bindings ++ kb.definitionBindings.filterNot(b => bound2(b.param.name)) ++ Wiring.calls(kb, bindings).filterNot(b => bound2(b.param.name))
    Fn.of(bs.size)(args => Flows.run[G](steps, bs.zip(args).toMap, impls, all)).asInstanceOf[s.Runs[G]]
