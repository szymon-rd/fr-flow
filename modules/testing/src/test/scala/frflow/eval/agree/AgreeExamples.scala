package frflow.eval.agree

import frflow.*
import scala.annotation.experimental

/** The code read from each class, run on drawn inputs and held to what the class itself gives on the JVM: the
  * result, and of a member that changes the class, the state after. An example is every case of one member; the
  * evaluator decides it on the terms (`check`'s "on the code"), and Rocq by running the generated definitions.
  */
@experimental class AgreeExamples extends FrFlowExamples(AgreeModel.model):
  import AgreeModel.*
  import Parcels.Parcel
  import Pure.*
  import Stateful.*

  private val draws = Draws(7)
  private val cases = 4
  private def all[A](inputs: List[A])(holds: A => Term[Boolean]): Term[Boolean] = inputs.map(holds).reduce(_ && _)

  private val sums = PlainArith(BigInt(5))
  example("numbers: arithmetic, an if, a val, an inline def and a method of the class"):
    all(draws.of(cases)((draws.number, draws.number)))((a, b) =>
      arith.blend(a, b).in(arith.holding(sums)) is sums.blend(a, b))
  example("truth values: comparisons and the connectives"):
    all(draws.of(cases)((draws.number, draws.number, draws.number)))((a, b, c) =>
      arith.ordered(a, b, c).in(arith.holding(sums)) is sums.ordered(a, b, c))

  private val zones = ZoneTariff(BigInt(4))
  example("an enum matched by its cases, a record's fields"):
    all(draws.of(cases)(draws.parcel))(p => tariff.price(p).in(tariff.holding(zones)) is zones.price(p))
  example("a record copied and made, an enum's case made"):
    all(draws.of(cases)((draws.parcel, draws.distance)))((p, km) =>
      tariff.reroute(p, km).in(tariff.holding(zones)) is zones.reroute(p, km))
  example("equality of data"):
    all(draws.of(cases)((draws.parcel, draws.parcel)))((p, q) =>
      (tariff.same(p, q).in(tariff.holding(zones)) is zones.same(p, q)) &&
        (tariff.same(p, p).in(tariff.holding(zones)) is zones.same(p, p)))
  example("a truth value computed into a record's field"):
    all(draws.of(cases)((draws.parcel, draws.number)))((p, limit) =>
      tariff.flagged(p, limit).in(tariff.holding(zones)) is zones.flagged(p, limit))

  private val options = PlainMaybe(BigInt(2))
  example("an option matched, its value or a default, its fold"):
    all(draws.of(cases)((draws.option, draws.option)))((a, b) =>
      maybe.total(a, b).in(maybe.holding(options)) is options.total(a, b))
  example("an option made, mapped, asked what holds of its value"):
    all(draws.of(cases)((draws.option, draws.number)))((a, limit) =>
      (maybe.pick(a, limit).in(maybe.holding(options)) is options.pick(a, limit)) &&
        (maybe.checks(a, limit).in(maybe.holding(options)) is options.checks(a, limit)))

  private val listed = PlainLists(BigInt(2))
  example("a list filtered, mapped and folded, its first member that fits"):
    all(draws.of(cases)((draws.parcels, draws.number)))((ps, limit) =>
      (lists.heavy(ps, limit).in(lists.holding(listed)) is listed.heavy(ps, limit)) &&
        (lists.load(ps).in(lists.holding(listed)) is listed.load(ps)) &&
        (lists.first(ps, limit).in(lists.holding(listed)) is listed.first(ps, limit)))
  example("a list made, joined and grown, its length, what holds of its members"):
    all(draws.of(cases)((draws.numbers, draws.number)))((xs, x) =>
      (lists.shape(xs, x).in(lists.holding(listed)) is listed.shape(xs, x)) &&
        (lists.facts(xs, x).in(lists.holding(listed)) is listed.facts(xs, x)))

  private val tabled = PlainTables(BigInt(1))
  example("a map read at a key and updated, a set asked of a member, a pair"):
    all(draws.of(cases)((draws.table, draws.name, draws.number)))((m, k, n) =>
      (tables.stock(m, k).in(tables.holding(tabled)) is tabled.stock(m, k)) &&
        (tables.restocked(m, k, n).in(tables.holding(tabled)) is tabled.restocked(m, k, n)) &&
        (tables.swap((n, k)).in(tables.holding(tabled)) is tabled.swap((n, k))))
  example("a set grown and joined, asked of a member"):
    all(draws.of(cases)((draws.tags, draws.tags, draws.name)))((s, u, t) =>
      tables.tagged(s, u, t).in(tables.holding(tabled)) is tabled.tagged(s, u, t))

  private def journalOf(entries: List[Parcel]) = ListJournal(BigInt(5), entries, BigInt(entries.size))
  example("a member that changes its class: the result, and the state after"):
    all(draws.of(cases)((draws.parcels, draws.parcel, draws.number)))((entries, p, limit) =>
      val (accepted, cleared) = (journalOf(entries), journalOf(entries))
      val (gave, removed) = (accepted.accept(p), cleared.clear(limit))
      val (accept, clear) = (journal.accept(p).in(journal.holding(journalOf(entries))),
        journal.clear(limit).in(journal.holding(journalOf(entries))))
      (accept.result is gave) && (accept.after === journal.holding(accepted)) && (clear.result is removed) &&
        (clear.after === journal.holding(cleared)) &&
        (journal.carried.in(accept.after) is accepted.carried) && (journal.holds(p.id).in(clear.after) is
          cleared.holds(p.id)))

  example("a class that holds two structures: what it gives, its state after, the held journal's with it"):
    all(draws.of(cases)((draws.parcels, draws.parcel)))((entries, p) =>
      val ran = TariffDepot(journalOf(entries), ZoneTariff(BigInt(4)), BigInt(10))
      val gave = ran.take(p)
      val take = depot.take(p).in(depot.holding(TariffDepot(journalOf(entries), ZoneTariff(BigInt(4)), BigInt(10))))
      (take.result is gave) && (take.after === depot.holding(ran)) && (depot.income.in(take.after) is ran.income))
