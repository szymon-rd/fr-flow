package frflow
package check
package proving

import cats.data.NonEmptyList
import cats.effect.IO
import frflow.lean.*
import frflow.protocol.*
import frflow.protocol.snapshot.Consistency

/** The FrModel as a whole (docs/DAG.md §3a): its statements hold together, and nothing they rest on is
  * vacuous. Lean is run on `Consistency.lean` once what it asks changes: the modules it imports built, then each
  * theorem judged (any of an item's theorems shows it).
  */
object Consistent:
  def hash(a: Analysis): Hash =
    val g = a.generate
    // The statements it is about as Lean states them too: their modules (and what those import) may change alone.
    val specs = g.witnessing.asked.flatMap(_.about).distinctBy(_.id).filter(g.formal).map(g.spec)
    Hash(Sha.parts(((g.witnessing.file :: specs) :+ analysis.CheckHash.CheckerVersion.toString)*))

  /** The recorded check, if still current. */
  def current(a: Analysis): Option[Consistency] = a.inputs.consistency.filter(_.hash == hash(a))

  def run(a: Analysis, lake: Lake): IO[Option[Consistency]] =
    val w = a.generate.witnessing
    if w.asked.isEmpty then IO.pure(None)
    else current(a).fold(check(a, lake, w))(c => IO.pure(Some(c)))

  private def check(a: Analysis, lake: Lake, w: Witnessing): IO[Option[Consistency]] =
    val layout = a.generate.layout
    val imports = """(?m)^import\s+(\S+)""".r.findAllMatchIn(w.file).map(_.group(1)).toList
    for
      built <- NonEmptyList.fromList(imports).fold(IO.pure(Run.built))(lake.build)
      run <- lake.elaborate(layout.consistency.path)
      e = Elaboration(w.file, run.output, layout.consistency.path)
      now <- IO.realTimeInstant
      c = Consistency(hash(a), w.asked.map(item(e, built, w, _)), now)
      _ <- frflow.ledger.Store.writeJson(a.ws.consistencyFile, io.circe.syntax.EncoderOps(c).asJson)
    yield Some(c)

  private def item(e: Elaboration, built: Run, w: Witnessing, asked: w.Asked): Consistency.Item =
    val proven = asked.theorems.map(_._1).find(t => e.verdict(t) == TheoremVerdict.Proven)
    val (status, detail) = (asked.missing, proven) match
      case (Some(why), _)         => (ObligationStatus.Open, why)
      case _ if !built.ok         => (ObligationStatus.Open, s"its imports do not build: ${Verdict.quoted(built)}")
      case (None, Some(_))        => (ObligationStatus.Proven, w.describe(asked))
      case (None, None)           =>
        val why = asked.theorems.headOption.flatMap((t, _) => e.verdict(t).why(t)).getOrElse("")
        (ObligationStatus.Open, s"Lean found no proof with ${asked.witness}: ${Verdict.clip(why, 2000)}")
    Consistency.Item(asked.kind, asked.about.map(n => NodeId(n.id)), asked.witness, status, detail)
