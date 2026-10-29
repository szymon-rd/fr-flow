package frflow.proof.lean

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.expr.{Binder, Lambda, Prog}
import frflow.core.name.*
import frflow.core.spec.{Form, Written}
import frflow.core.term.*
import frflow.core.ty.*
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.*
import frflow.proof.lean.term.Printed
import frflow.proof.terms.{OpenTerms, TermTable}

/** crm's expiry job, written as elaboration gives it: `ExpiryJob`'s post as a term over its inputs, `expireOnce`'s
  * recorded steps (their terms terms too), and the lowering environment of the crm FrModel for them.
  */
object ExpiryIr:
  private val store = Ty.Data(TypeName("CrmStore"))
  private val event = Ty.Data(TypeName("Event"))
  private val tables = Ty.Data(TypeName("Tables"))
  private val big = Ty.Num(NumKind.Big)
  private def v(i: Int, hint: String, t: Ty) = Binder(VarId.level(i), hint, t)

  private val data: Map[TypeName, DataType] = Map(
    TypeName("Tables") -> DataType.Product(TypeName("Tables"), "Tables",
      List(Field("store", store), Field("events", Ty.ListOf(event)))),
    TypeName("Event") -> DataType.Sum(TypeName("Event"), "Event",
      NonEmptyList.one(Ctor(CtorName("Expired"), List(Field("at", big))))))

  /** `expireOnce` is over `expire` (its open term); the other defines over none. */
  val env: LowerEnv = LowerEnv(KbName("Crm"), d => Option.when(d.value == "expireOnce")(Names.ident("expire")).toList,
    _ => Names.builtin("databaseModel"),
    op => LExpr.Const(List(Names.builtin("DatabaseModel.Ops"), Names.ident(op.value))), data.get,
    _ => Some(store))
  val reserved: Naming = Naming.over(Set("expire"), Set("CrmStore", "Tables", "Event", "World"))

  /** The terms the job's statements and steps are made of, for any interpreter. */
  private final class Parts[T[_]](s: Sym[T]):
    private def sel[F](name: String, i: Int, ty: Ty) =
      Selector[Any, F](name, i, TypeName("Tables"), ty, _ => sys.error("printed only"), (r, _) => r)
    def expire(st: T[Any], now: T[BigInt]): T[Any] =
      s.app(s.app(s.param[Any => BigInt => Any](SymbolName("expire"), Ty.FnOf(List(store, big), store)), st), now)
    def expired(now: T[BigInt]): T[Any] =
      s.app(s.construct(Constructor[BigInt => Any](TypeName("Event"), CtorName("Expired"), n => n)), now)
    def part(w: Binder): T[Any] = s.part[Any](s.free[World](w), ModelName("DatabaseModel"), tables)
    def storeOf(w: Binder): T[Any] = s.field(part(w), sel[Any]("store", 0, store))
    def eventsOf(w: Binder): T[List[Any]] = s.field(part(w), sel[List[Any]]("events", 1, Ty.ListOf(event)))

  private val (now, result, before, after) = (v(0, "now", big), v(1, "result", store), v(2, "before", Ty.World),
    v(3, "after", Ty.World))

  val post: Written[Lambda] = Written.lambda(List(now, result, before, after), [T[_]] => (s: Sym[T]) =>
    val p = Parts(s)
    val sameRows = Body[Any => Any => Boolean](DefName("sameRows"), Ty.FnOf(List(store), Ty.FnOf(List(store),
      Ty.Bool)), [U[_]] => (_: Sym[U]) => sys.error("printed only"))
    val rows = s.app(s.app(s.define(sameRows), p.storeOf(after)), p.expire(p.storeOf(before), s.free(now)))
    val events = s.eq(p.eventsOf(after), s.append(p.eventsOf(before), s.cons(p.expired(s.free(now)), s.nil(event))))
    s.and(s.and(rows, events), s.eq(s.free[Any](result), p.expire(p.storeOf(before), s.free(now)))),
    SourceText("…"))

  private def term[A](t: [T[_]] => Sym[T] => T[A]): Stated[?] = Stated(t)
  private def call(op: String, args: Stated[?]*) =
    Prog.Call(SymbolName(op), args.toList, Ty.Unit)

  val expireOnce: Written[Lambda] =
    val (n, st, t, id) = (v(0, "now", big), v(11, "s", store), v(12, "t", store), v(13, "id", big))
    val (w1, w2) = (v(14, "_$1", Ty.Unit), v(15, "_$2", Ty.Unit))
    val changed = Body[Any => Any => List[BigInt]](DefName("changedIds"), Ty.FnOf(List(store),
      Ty.FnOf(List(store), Ty.ListOf(big))), [U[_]] => (_: Sym[U]) => sys.error("printed only"))
    val steps = Prog.Bind(Prog.Call(SymbolName("load"), Nil, store), st,
      Prog.Let(t, term([T[_]] => (s: Sym[T]) => Parts(s).expire(s.free(st), s.free(n))),
        Prog.Bind(Prog.Loop(term([T[_]] => (s: Sym[T]) => s.app(s.app(s.define(changed), s.free[Any](st)),
          s.free[Any](t))), id, call("storeAbout", term([T[_]] => (s: Sym[T]) => s.free[BigInt](id)),
          term([T[_]] => (s: Sym[T]) => s.free[Any](t)))), w1,
        Prog.Bind(call("logEvent", term([T[_]] => (s: Sym[T]) => Parts(s).expired(s.free(n)))), w2,
          Prog.Pure(term([T[_]] => (s: Sym[T]) => s.free[Any](t)))))))
    Written.steps(List(n), steps, store, SourceText("…"))

  val expiryJob: NodeId = NodeId("ExpiryJob")
  val sharesExpire: NodeId = NodeId("SharesExpire")
  val expireOnceRun: DefName = DefName("expireOnce_run")

  /** The open terms of the two claims and of `expireOnce_run`, and the symbols' types, as `TermTable.of` gives them. */
  val table: TermTable = TermTable(
    claims = Map(expiryJob -> terms("expire", "runExpiry"), sharesExpire -> terms("expire")),
    posts = Map.empty, defines = Map(expireOnceRun -> terms("expire")),
    types = Map(SymbolName("expire") -> Ty.FnOf(List(store, big), store),
      SymbolName("runExpiry") -> Ty.FnOf(List(big), Ty.FlowOf(store, None))))

  private def terms(symbols: String*) = OpenTerms(Nil, symbols.toList.map(SymbolName(_)))

  /** A lambda printed as a declaration's value, from its term (`Printed`) or its recorded steps (`LowerProg`). */
  def lowered(w: Written[Lambda]): LExpr = w.form match
    case Form.Term(t)  =>
      val (bs, body) = Printed.define(env, reserved)(w.value.params, t.run)
      LExpr.Fun(bs, body)
    case Form.Steps(p) =>
      val inputs = w.value.params
      val (bs, lines) = (inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty)))),
        LowerProg(env, inputs.size).block(p)).tupled.runA(reserved).value
      LExpr.Fun(bs, LExpr.Do(lines, 4))
