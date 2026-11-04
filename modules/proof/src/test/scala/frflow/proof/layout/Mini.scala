package frflow.proof.layout

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.example.Example
import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.name.{DefName, NodeId, SourceText, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}

/** A small FrModel reaching every kind of module: the store of bookings and its program `book` (proven code,
  * `impl`, `root_impl`), what always holds of a booking (`cover_book`, `start_`, `inhabited_`), and a Declaration
  * refined by one claim (`complete`, the tries, a consistency group FrFlow witnesses), with an example.
  */
object Mini:
  private val big = Lang.big
  private val test = Ty.FnOf(List(big), Ty.Bool)
  private def rule(name: String, x: Binder)(body: Final[Boolean]): Define =
    Define(DefName(name), Written.lambda(List(x), body, SourceText(name)), DefineForm.Function)
  private val b = Binder(VarId.level(0), "b", Booking.ty)
  private val held = Binder(VarId.level(0), "held", Ty.ListOf(Booking.ty))

  /** `b.start < b.end`: the rule of `endsAfterStart`, a define named as the node. */
  private val endsRule = rule("endsAfterStart", b)([T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)))
  private val emptyRule = rule("startsEmpty", held)([T[_]] => (s: Sym[T]) =>
    s.eq(s.free[List[Booking]](held), s.nil[Booking](Booking.ty)))
  private val run = Define(DefName("bookIfFree_run"), Store.program.written, DefineForm.RunOf(DefName("bookIfFree")))

  val endsAfterStart: frflow.core.spec.Node = claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x =>
      l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end)))))

  private def allowed[T[_]](l: Lang[T], n: T[BigInt]): T[Boolean] = l.call(l.sym[BigInt => Boolean]("allowed", test), n)
  val allowedPositive: frflow.core.spec.Node = claim("allowedPositive")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("n", big)(n => l.s.eq(allowed(l, n), l.s.lt(l.num(0), n)))))
  val allowsOne: frflow.core.spec.Node =
    claim("allowsOne")(Lang.formula([T[_]] => (l: Lang[T]) => allowed(l, l.num(1))))

  val kb: Kb = Store.kb.and(endsAfterStart, allowedPositive, allowsOne,
      outside("startsEmpty")(OutsideFact.Initially(Store.model, DefName("startsEmpty"))),
      assumption("fromTheForm")(Lang.formula([T[_]] => (l: Lang[T]) =>
      l.s.always(Bound[Booking]("b", Booking.ty))(x =>
        l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))))
    .declaring(v => v.copy(defines = v.defines ++ List(run, endsRule, Fixture.rule("fromTheForm"), emptyRule)))
    .naming(declaration("allowed", test))
    .linking(partOf("allowedPositive", "allowsOne"))
    .linking(List("onlyCode", "oneAtATime", "startsEmpty", "fromTheForm")
      .map(assumes("endsAfterStart", _))*)
    .linking(assumes("bookRuns", "fromTheForm"))

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))

  val examples: List[Example] = List(Example("two is allowed", Nil, Written.formula(Lang.formula([T[_]] =>
    (l: Lang[T]) => allowed(l, l.num(2))), SourceText("allowed(2) is true"))))

  /** The value the witness search would find for `endsAfterStart`. */
  val booking: Value = Value.Data(Booking.make.ctor, List(Value.Str(""), Value.Num(0), Value.Num(1)))
  val endsAfterStartId: NodeId = NodeId("endsAfterStart")
