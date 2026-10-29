package frflow.proof.layout.failing

import frflow.core.{Booking, Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.expr.{Prog, Value}
import frflow.core.name.{DefName, ModelName, SymbolName}
import frflow.core.term.{Bound, Final, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Fails, ModelOp, StateModel}
import frflow.proof.layout.Fixture.*

/** Programs that may fail, on a shelf of bookings any call of which may fail with `"down"`, changing nothing:
  * `file` puts a booking (crm's shape: what a run gives, and what a failed one does, `.failing { (error, after) =>
  * … }`); `check` gives the booking it is given or raises (sharing's shape: a failed run changes nothing,
  * `.failsChangingNothing[String]`), its result a booking (`made_check`, of the runs that succeed); `spoil` puts a
  * booking and, when the shelf is down, puts it backwards and fails: what it leaves when it fails breaks
  * `endsAfterStart`, so its `cover_` must not be proven; `fileTwice` puts the booking twice at once, which commutes
  * whichever call fails (`commute_0`, through `FrFlow.runOnE`). `fileWrong` says a failed run of `file` holds the
  * booking: false, so its `impl` must not be proven.
  */
object Failing:
  private val shelf = ModelName("shelved")
  private val (b, held, e) = (at(0, "b", Booking.ty), at(1, "held", Ty.ListOf(Booking.ty)), step(1, "e", Ty.Str))
  private val model = StateModel(shelf, "a shelf of bookings that may be down", Ty.ListOf(Booking.ty), List(
    ModelOp(SymbolName("put"), List(b), Ty.Unit, Prog.Modify(shelf, held, term([T[_]] => (s: Sym[T]) =>
      s.cons(s.free[Booking](b), s.free[List[Booking]](held)))))), Some(Fails(Ty.Str, Value.Str("down"))))

  private def put(x: Stated[Booking]) = Prog.Call(SymbolName("put"), List(x), Ty.Unit)
  private def raise(why: String) = Prog.Raise(term([T[_]] => (s: Sym[T]) => Lang(s).str(why)))
  private val backwards = term([T[_]] => (s: Sym[T]) => booking(s, s.field(s.free[Booking](b), room),
    s.field(s.free[Booking](b), Booking.end), s.field(s.free[Booking](b), Booking.start)))
  private val endsLater = term([T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)))
  private val checking = Prog.Branch(endsLater, Prog.Pure(v[Booking](b)), raise("backwards"))
  private val spoiling = Prog.Catch(put(v(b)), Ty.Str, e, Prog.Bind(put(backwards), step(0, "u", Ty.Unit),
    Prog.Raise(v[String](e))))

  private val pair = Ty.TupleOf(List(Ty.Unit, Ty.Unit))
  private val twice = Prog.Par(put(v(b)), step(0, "u", Ty.Unit), put(v(b)), step(1, "u2", Ty.Unit))

  private def program(out: Ty): Ty = fn(Booking.ty, Ty.FlowOf(out, None))
  private def run[T[_], R](l: Lang[T], name: String, out: Ty, x: T[Booking]): T[Program[R]] =
    l.call(l.sym[Booking => Program[R]](name, program(out)), x)
  private def shelved[T[_]](l: Lang[T], w: T[World]): T[List[Booking]] =
    l.s.part[List[Booking]](w, shelf, Ty.ListOf(Booking.ty))
  private val after = Bound[World]("after", Ty.World)

  /** `file(b).from(before) { (_, after) => after.shelved = b :: before.shelved }.failing { (error, after) =>
    * error = "down" && after.shelved = before.shelved }`.
    */
  private val fileRuns: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[Booking]("b", Booking.ty)(x =>
    l.forall[World]("before", Ty.World)(w => l.s.and(
      l.s.runs(run[T, Unit](l, "file", Ty.Unit, x), w, Bound[Unit]("r", Ty.Unit), after)((_, a) =>
        l.s.eq(shelved(l, a), l.s.cons(x, shelved(l, w)))),
      l.s.fails(run[T, Unit](l, "file", Ty.Unit, x), w, Bound[String]("error", Ty.Str), after)((err, a) =>
        l.s.and(l.s.eq(err, l.str("down")), l.s.eq(shelved(l, a), shelved(l, w))))))))

  /** `file(b).from(before) { (_, _) => true }.failing { (_, after) => after.shelved = b :: before.shelved }`. */
  private val fileWrong: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[Booking]("b", Booking.ty)(x =>
    l.forall[World]("before", Ty.World)(w => l.s.and(
      l.s.runs(run[T, Unit](l, "file", Ty.Unit, x), w, Bound[Unit]("r", Ty.Unit), after)((_, _) => l.truth),
      l.s.fails(run[T, Unit](l, "file", Ty.Unit, x), w, Bound[String]("error", Ty.Str), after)((_, a) =>
        l.s.eq(shelved(l, a), l.s.cons(x, shelved(l, w))))))))

  /** `check(b).from(before) { (r, after) => r = b && unchanged(after, before) }.failsChangingNothing[String]`: no
    * model's state changes, whatever the faults.
    */
  private val checkRuns: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[Booking]("b", Booking.ty)(x =>
    l.forall[World]("before", Ty.World)(w => l.s.and(
      l.s.runs(run[T, Booking](l, "check", Booking.ty, x), w, Bound[Booking]("r", Booking.ty), after)((r, a) =>
        l.s.and(l.s.eq(r, x), l.s.unchanged(a, w))),
      l.s.fails(run[T, Booking](l, "check", Booking.ty, x), w, Bound[String]("error", Ty.Str), after)((_, a) =>
        l.s.unchanged(a, w))))))

  private val facts = storeFacts(shelf)
  private val runClaims = List(claim("fileRuns")(fileRuns), claim("fileWrong")(fileWrong),
    claim("checkRuns")(checkRuns),
    claim("spoilRuns")(runs[Booking, Unit]("spoil", Booking.ty, Ty.Unit)),
    claim("twiceRuns")(runs[Booking, (Unit, Unit)]("fileTwice", Booking.ty, pair)))

  val kb: Kb = Kb.of((List(endsAfterStart, fromOutside("fromOutside")) ++ runClaims ++ facts)*)
    .modelling(model)
    .declaring(_.copy(types = List(Booking.data), defines = List(endsRule, rule("fromOutside"), emptyRule) ++
        flow("fileIt", List(b), put(v(b)), Ty.Unit) ++
        flow("checkIt", List(b), checking, Booking.ty) ++ flow("spoilIt", List(b), spoiling, Ty.Unit) ++
        flow("fileBoth", List(b), twice, pair)))
    .naming(definition("file", program(Ty.Unit)), definition("check", program(Booking.ty)),
      definition("spoil", program(Ty.Unit)), definition("fileTwice", program(pair)))
    .coding(SymbolName("file") -> Code.ProvenFlow(DefName("fileIt")),
      SymbolName("check") -> Code.ProvenFlow(DefName("checkIt")),
      SymbolName("spoil") -> Code.ProvenFlow(DefName("spoilIt")),
      SymbolName("fileTwice") -> Code.ProvenFlow(DefName("fileBoth")))
    .linking(("fromOutside" :: facts.map(_.id.value)).map(assumes("endsAfterStart", _))*)
    .linking(List("shelfOneRun", "fromOutside").flatMap(f =>
      List("fileRuns", "fileWrong", "spoilRuns", "twiceRuns").map(c => assumes(c, f))) :+
      assumes("checkRuns", "fromOutside")*)

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))
