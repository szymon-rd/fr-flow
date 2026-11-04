package frflow.proof.lean

import frflow.core.expr.{Binder, Prog}
import frflow.core.name.*
import frflow.core.term.*
import frflow.core.ty.*
import frflow.core.vocab.{ModelOp, StateModel}

/** crm's database model as elaboration gives it: each operation's steps on the model's `Tables` as its `means`
  * records them.
  */
object CrmModels:
  private val store = Ty.Data(TypeName("CrmStore"))
  private val event = Ty.Data(TypeName("Event"))
  private val tables = Ty.Data(TypeName("Tables"))
  private val big = Ty.Num(NumKind.Big)
  private val name = ModelName("databaseModel")
  private def v(i: Int, hint: String, t: Ty) = Binder(VarId.level(i), hint, t)

  private val (t, e, id, about, after) =
    (v(0, "t", tables), v(0, "e", event), v(0, "id", big), v(1, "t", store), v(2, "t", tables))

  val model: StateModel = StateModel(name,
    "the SQLite database the CRM keeps its records, shares, expiries and event log in.", tables, List(
    ModelOp(SymbolName("load"), Nil, store, Prog.Bind(Prog.Read(name), t,
      Prog.Pure(term([T[_]] => (s: Sym[T]) => Parts(s).storeOf(t))))),
    ModelOp(SymbolName("logEvent"), List(e), Ty.Unit, Prog.Modify(name, v(1, "t", tables), term([T[_]] => (s: Sym[T]) =>
      val p = Parts(s)
      p.tables(p.storeOf(v(1, "t", tables)),
        s.append(p.eventsOf(v(1, "t", tables)), s.cons(s.free[Any](e), s.nil[Any](event))))))),
    ModelOp(SymbolName("storeAbout"), List(id, about), Ty.Unit, Prog.Modify(name, after, term([T[_]] => (s: Sym[T]) =>
      val p = Parts(s)
      val record = p.aboutRecord(s.free[Any](about), s.free[BigInt](id))
      p.tables(p.replaceAbout(p.storeOf(after), s.free[BigInt](id), record), p.eventsOf(after)))))), None)

  private def term[A](t: [T[_]] => Sym[T] => T[A]): Stated[?] = Stated(t)

  private final class Parts[T[_]](s: Sym[T]):
    private def sel[F](n: String, i: Int, ty: Ty) =
      Selector[Any, F](n, i, TypeName("Tables"), ty, _ => sys.error("printed only"), (r, _) => r)
    def storeOf(w: Binder): T[Any] = s.field(s.free[Any](w), sel[Any]("store", 0, store))
    def eventsOf(w: Binder): T[List[Any]] = s.field(s.free[Any](w), sel[List[Any]]("events", 1, Ty.ListOf(event)))
    def tables(st: T[Any], es: T[List[Any]]): T[Any] =
      s.app(s.app(s.construct(Constructor[Any => List[Any] => Any](TypeName("Tables"), CtorName("mk"), a => _ => a)),
        st), es)
    /** `aboutRecord t id` and `replaceAbout s id r`: defines of the crm FrModel, called by name. */
    def aboutRecord(t: T[Any], id: T[BigInt]): T[Any] = s.app(s.app(s.define(named[Any => BigInt => Any](
      "aboutRecord", List(store, big))), t), id)
    def replaceAbout(st: T[Any], id: T[BigInt], r: T[Any]): T[Any] = s.app(s.app(s.app(s.define(
      named[Any => BigInt => Any => Any]("replaceAbout", List(store, big, store))), st), id), r)
    private def named[F](d: String, ins: List[Ty]): Body[F] =
      Body[F](DefName(d), Ty.FnOf(ins, store), [U[_]] => (_: Sym[U]) => sys.error("printed only"))
