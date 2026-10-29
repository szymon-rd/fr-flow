package frflow.proof.layout

import frflow.core.{Booking, Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.expr.Prog
import frflow.core.name.{DefName, ModelName, SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.Sym
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, ModelOp, StateModel}
import Fixture.*

/** Proven code that breaks what always holds, and steps at once on a store: `misdate` makes a booking ending before
  * it starts (its `made_` must not be proven), `fileBackwards` stores one (its `cover_` must stay open); `countBoth`
  * reads the store twice at once (its branches commute), `putTwo` adds two bookings at once (they do not: the order
  * they are added in is the order they are held in).
  */
object Broken:
  private val big = Lang.big
  private val shelf = ModelName("shelved")
  private val (b, held, h) = (at(0, "b", Booking.ty), at(1, "held", Ty.ListOf(Booking.ty)),
    step(0, "h", Ty.ListOf(Booking.ty)))
  private val model = StateModel(shelf, "a shelf of bookings", Ty.ListOf(Booking.ty), List(
    ModelOp(SymbolName("put"), List(b), Ty.Unit, Prog.Modify(shelf, held, term([T[_]] => (s: Sym[T]) =>
      s.cons(s.free[Booking](b), s.free[List[Booking]](held))))),
    ModelOp(SymbolName("count"), Nil, big, Prog.Bind(Prog.Read(shelf), h,
      Prog.Pure(term([T[_]] => (s: Sym[T]) => s.length(s.free[List[Booking]](h))))))), None)

  /** The booking `b` asks for, its start and end swapped. */
  private def swapped[T[_]](s: Sym[T]): T[Booking] = booking(s, s.field(s.free[Booking](b), room),
    s.field(s.free[Booking](b), Booking.end), s.field(s.free[Booking](b), Booking.start))
  private val swap = Define(DefName("swap"), Written.lambda(List(b), [T[_]] => (s: Sym[T]) => swapped(s),
    SourceText("swap")), DefineForm.Function)
  private def put(x: frflow.core.term.Stated[Booking]) = Prog.Call(SymbolName("put"), List(x), Ty.Unit)
  private val count = Prog.Call(SymbolName("count"), Nil, big)
  private val later = term([T[_]] => (s: Sym[T]) => booking(s, s.field(s.free[Booking](b), room),
    s.field(s.free[Booking](b), Booking.start), s.add(s.field(s.free[Booking](b), Booking.end), Lang(s).num(1))))
  private val (u1, u2, n1, n2) = (step(0, "u", Ty.Unit), step(1, "u2", Ty.Unit), step(2, "n", big), step(3, "m", big))
  private val pair = Ty.TupleOf(List(Ty.Unit, Ty.Unit))

  private val misdateSame = claim("misdateSame")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.s.eq(l.s.field(l.call(l.sym[Booking => Booking]("misdate",
      fn(Booking.ty, Booking.ty)), x), room), l.s.field(x, room)))))
  private val facts = storeFacts(shelf)
  private val runClaims = List(claim("filedRuns")(runs[Booking, Unit]("fileBackwards", Booking.ty, Ty.Unit)),
    claim("countRuns")(runsAlone[(BigInt, BigInt)]("countBoth", Ty.TupleOf(List(big, big)))),
    claim("putRuns")(runs[Booking, (Unit, Unit)]("putTwo", Booking.ty, pair)))

  val kb: Kb = Kb.of((List(endsAfterStart, fromOutside("fromOutside"), misdateSame) ++ runClaims ++ facts)*)
    .modelling(model)
    .declaring(_.copy(types = List(Booking.data), defines = List(endsRule, rule("fromOutside"), emptyRule, swap) ++
        flow("fileBack", List(b), put(term([T[_]] => (s: Sym[T]) => swapped(s))), Ty.Unit) ++
        flow("countTwice", Nil, Prog.Par(count, n1, count, n2), Ty.TupleOf(List(big, big))) ++
        flow("putBoth", List(b), Prog.Par(put(v(b)), u1, put(later), u2), pair)))
    .naming(definition("misdate", fn(Booking.ty, Booking.ty)),
      definition("fileBackwards", fn(Booking.ty, Ty.FlowOf(Ty.Unit, None))),
      definition("countBoth", Ty.FlowOf(Ty.TupleOf(List(big, big)), None)), definition("putTwo", fn(Booking.ty,
        Ty.FlowOf(pair, None))))
    .coding(SymbolName("misdate") -> Code.Proven(DefName("swap")),
      SymbolName("fileBackwards") -> Code.ProvenFlow(DefName("fileBack")),
      SymbolName("countBoth") -> Code.ProvenFlow(DefName("countTwice")),
      SymbolName("putTwo") -> Code.ProvenFlow(DefName("putBoth")))
    .linking(("fromOutside" :: facts.map(_.id.value)).map(assumes("endsAfterStart", _))*)
    .linking(List("shelfOneRun", "fromOutside").flatMap(f =>
      runClaims.map(c => assumes(c.id.value, f))) :+ assumes("misdateSame", "fromOutside")*)

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))
