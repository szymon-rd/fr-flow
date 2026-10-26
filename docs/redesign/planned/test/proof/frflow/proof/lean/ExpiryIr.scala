package frflow.proof.lean

import cats.data.NonEmptyList
import frflow.core.expr.*
import frflow.core.name.*
import frflow.core.ty.*
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.*
import frflow.proof.terms.{OpenTerms, TermTable}

/** The IR of crm's expiry job, written by hand as elaboration gives it: `ExpiryJob`'s post and `expireOnce`'s steps,
  * and the lowering environment of the crm knowledge base for them.
  */
object ExpiryIr:
  private val store = Ty.Data(TypeName("CrmStore"))
  private val event = Ty.Data(TypeName("Event"))
  private val tables = Ty.Data(TypeName("Tables"))
  private val big = Ty.Num(NumKind.Big)
  private def v(i: Int, hint: String, t: Ty) = Binder(VarId(i), hint, t)

  private val data: Map[TypeName, DataType] = Map(
    TypeName("Tables") -> DataType.Product(TypeName("Tables"), "Tables",
      List(Field("store", store), Field("events", Ty.ListOf(event)))),
    TypeName("Event") -> DataType.Sum(TypeName("Event"), "Event",
      NonEmptyList.one(Ctor(CtorName("Expired"), List(Field("at", big))))))

  val env: LowerEnv = LowerEnv(KbName("Crm"), _ => Nil, _ => Names.builtin("database"), _ => Names.builtin("Database"),
    data.get)
  val reserved: Naming = Naming.over(Set("expire"), Set("CrmStore", "Tables", "Event", "World"))

  private val expire = Expr.Sym(SymbolName("expire"), Ty.FnOf(List(store, big), store))
  private def expireOf(s: Expr, now: Expr) = Expr.Apply(expire, List(s, now), store)
  private def expired(now: Expr) = Expr.Make(TypeName("Event"), CtorName("Expired"), List(now))
  private def part(w: Binder, field: Int, t: Ty) =
    Expr.Field(Expr.Part(Expr.Var(w), ModelName("DatabaseModel"), tables), TypeName("Tables"), field, t)
  private def and(a: Expr, b: Expr) = Expr.Prim(PrimOp.And, List(a, b), Ty.Bool)
  private def eq(a: Expr, b: Expr) = Expr.Prim(PrimOp.Eq, List(a, b), Ty.Bool)

  val post: Lambda =
    val (now, result, before, after) = (v(0, "now", big), v(1, "result", store), v(2, "before", Ty.World),
      v(3, "after", Ty.World))
    val rows =
      Expr.Call(DefName("sameRows"), List(part(after, 0, store), expireOf(part(before, 0, store), Expr.Var(now))),
      Ty.Bool)
    val events = eq(part(after, 1, Ty.ListOf(event)), Expr.Prim(PrimOp.Append,
      List(part(before, 1, Ty.ListOf(event)), Expr.ListOf(List(expired(Expr.Var(now))), event)), Ty.ListOf(event)))
    Lambda(List(now, result, before, after),
      and(and(rows, events), eq(Expr.Var(result), expireOf(part(before, 0, store), Expr.Var(now)))), Ty.Bool)

  private def call(op: String, args: Expr*) = Prog.Call(BoundaryName("database"), OpName(op), args.toList, Ty.Unit)

  val expireOnce: Lambda =
    val (now, s, t, id) = (v(10, "now", big), v(11, "s", store), v(12, "t", store), v(13, "id", big))
    val (w1, w2) = (v(14, "_$1", Ty.Unit), v(15, "_$2", Ty.Unit))
    val steps = Prog.Bind(Prog.Call(BoundaryName("database"), OpName("load"), Nil, store), s,
      Prog.Let(t, expireOf(Expr.Var(s), Expr.Var(now)),
        Prog.Bind(Prog.Loop(Expr.Call(DefName("changedIds"), List(Expr.Var(s), Expr.Var(t)), Ty.ListOf(big)), id,
          call("storeAbout", Expr.Var(id), Expr.Var(t))), w1,
        Prog.Bind(call("logEvent", expired(Expr.Var(now))), w2, Prog.Pure(Expr.Var(t))))))
    Lambda(List(now), Expr.Do(steps, Ty.FlowOf(store)), Ty.FlowOf(store))

  val expiryJob: NodeId = NodeId("ExpiryJob")
  val sharesExpire: NodeId = NodeId("SharesExpire")
  val expireOnceRun: DefName = DefName("expireOnce_run")

  /** The open terms of the two claims and of `expireOnce_run`, and the symbols' types, as `TermTable.of` gives them. */
  val table: TermTable = TermTable(
    claims = Map(expiryJob -> terms("expire", "runExpiry"), sharesExpire -> terms("expire")),
    posts = Map.empty, expected = Map.empty, defines = Map(expireOnceRun -> terms("expire")),
    types = Map(SymbolName("expire") -> Ty.FnOf(List(store, big), store),
      SymbolName("runExpiry") -> Ty.FnOf(List(big), Ty.FlowOf(store))),
    fixings = Map.empty)

  private def terms(symbols: String*) = OpenTerms(Nil, symbols.toList.map(SymbolName(_)))

  /** A lambda lowered as a declaration's value: `fun (x : T) … => body`. */
  def lowered(l: Lambda): LExpr =
    val (bs, body) = Lower(env).lambda(l).runA(reserved).value
    LExpr.Fun(bs, body)
