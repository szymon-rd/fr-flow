package frflow.proof.layout

import frflow.core.analysis.resolution.{Resolve, Resolved}
import frflow.core.analysis.Validate
import frflow.core.{Booking, Desk, Kb, Lang}
import frflow.core.example.Example
import frflow.core.expr.{Binder, Value}
import frflow.core.name.{DefName, NodeId, SourceText, VarId}
import frflow.core.Nodes.*
import frflow.core.spec.Written
import frflow.core.term.Bound
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}

/** A small FrModel reaching every kind of module: the booking desk and its Definition `book` (proven code, `impl`,
  * `root_impl`), what always holds of a booking (`inhabited_`), and a Declaration refined by one claim (`complete`,
  * the tries, a consistency group FrFlow witnesses), with an example.
  */
object Mini:
  private val big = Lang.big
  private val test = Ty.FnOf(List(big), Ty.Bool)
  private def rule(name: String, x: Binder)(body: Final[Boolean]): Define =
    Define(DefName(name), Written.lambda(List(x), body, SourceText(name)), DefineForm.Function)
  private val b = Binder(VarId.level(0), "b", Booking.ty)

  /** `b.start < b.end`: the rule of `endsAfterStart`, a define named as the node. */
  private val endsRule = rule("endsAfterStart", b)([T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)))

  val endsAfterStart: frflow.core.spec.Node = claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x =>
      l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end)))))

  private def allowed[T[_]](l: Lang[T], n: T[BigInt]): T[Boolean] = l.call(l.sym[BigInt => Boolean]("allowed", test), n)
  val allowedPositive: frflow.core.spec.Node = claim("allowedPositive")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("n", big)(n => l.s.eq(allowed(l, n), l.s.lt(l.num(0), n)))))
  val allowsOne: frflow.core.spec.Node =
    claim("allowsOne")(Lang.formula([T[_]] => (l: Lang[T]) => allowed(l, l.num(1))))

  val kb: Kb = Desk.kb.and(endsAfterStart, allowedPositive, allowsOne,
      assumption("fromTheForm")(Lang.formula([T[_]] => (l: Lang[T]) =>
      l.s.always(Bound[Booking]("b", Booking.ty))(x =>
        l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))))
    .declaring(v => v.copy(defines = v.defines ++ List(endsRule, Fixture.rule("fromTheForm"))))
    .naming(declaration("allowed", test))
    .linking(partOf("allowedPositive", "allowsOne"))
    .linking(assumes("endsAfterStart", "fromTheForm"), assumes("bookRuns", "fromTheForm"))

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))

  val examples: List[Example] = List(Example("two is allowed", Nil, Written.formula(Lang.formula([T[_]] =>
    (l: Lang[T]) => allowed(l, l.num(2))), SourceText("allowed(2) is true")), "Mini", 0))

  /** The value the witness search would find for `endsAfterStart`. */
  val booking: Value = Value.Data(Booking.make.ctor, List(Value.Str(""), Value.Num(0), Value.Num(1)))
  val endsAfterStartId: NodeId = NodeId("endsAfterStart")
