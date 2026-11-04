package frflow.proof.layout.calls

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.expr.{Binder, OutsideFact, Prog}
import frflow.core.name.{DefName, ModelName, SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, ModelOp, StateModel}
import frflow.proof.layout.Fixture.*

/** The crm-shaped job of `Rows` reading its rows back from a second store, `held`, which it writes as it goes (review
  * 11b, R1). An operation's result is trusted to meet the rules only while nothing before it in the run wrote its
  * store; a loop's earlier iterations and a handler's body run before, though they come after in the text. Each job
  * here hands `storeAbout` rows it has just written twice, and its `made_` at that call stays open:
  * - `inLoop`: for each of `[key, key, key]`, read the held rows, store them, put the key; then clear;
  * - `inHandler`: put the key twice and fail; the handler reads the held rows and stores them; then clear.
  */
object Reuse:
  private val big = Lang.big
  private val keys = Ty.ListOf(big)
  private val (tables, held) = (ModelName("tables"), ModelName("held"))
  private val (key, rows) = (at(0, "key", big), at(1, "rows", keys))
  private val (state, k) = (at(1, "state", keys), at(0, "k", big))
  private val database = StateModel(tables, "the database's tables: how many rows they hold", big, List(
    ModelOp(SymbolName("storeAbout"), List(key, rows), Ty.Unit, Prog.Write(tables,
      term([T[_]] => (s: Sym[T]) => s.length(s.free[List[BigInt]](rows)))))), None)
  private val read = step(9, "now", keys)
  private val heldModel = StateModel(held, "the keys the job holds", keys, List(
    ModelOp(SymbolName("heldKeys"), Nil, keys, Prog.Bind(Prog.Read(held), read, Prog.Pure(v[List[BigInt]](read)))),
    ModelOp(SymbolName("put"), List(k), Ty.Unit, Prog.Modify(held, state, term([T[_]] => (s: Sym[T]) =>
      s.append(s.free[List[BigInt]](state), s.cons(s.free[BigInt](k), s.nil[BigInt](big)))))),
    ModelOp(SymbolName("clear"), Nil, Ty.Unit, Prog.Write(held, term([T[_]] => (s: Sym[T]) => s.nil[BigInt](big))))),
    None)

  private val listed = at(0, "rows", keys)
  private def rule(name: String)(body: [T[_]] => (Sym[T], T[List[BigInt]]) => T[Boolean]) =
    Define(DefName(name), Written.lambda(List(listed), [T[_]] => (s: Sym[T]) =>
      body[T](s, s.free[List[BigInt]](listed)), SourceText(name)), DefineForm.Function)
  private val nodup = [T[_]] => (s: Sym[T], xs: T[List[BigInt]]) => s.nodup(xs)
  private val each = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[List[BigInt]]("rows", keys))(x => l.s.nodup(x)))
  /** What the store holds holds each key once. */
  private val heldOnce = claim("heldOnce")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[World]("w", Ty.World))(w => l.s.nodup(l.s.part[List[BigInt]](w, held, keys)))))

  private def call(op: String, args: Stated[?]*): Prog[Stated[?]] = Prog.Call(SymbolName(op), args.toList, Ty.Unit)
  private def andThen(first: Prog[Stated[?]], i: Int, rest: Prog[Stated[?]]) =
    Prog.Bind(first, step(i, s"u$i", Ty.Unit), rest)
  private val r = step(0, "r", keys)
  private def readAndStore(x: Binder): Prog[Stated[?]] = Prog.Bind(Prog.Call(SymbolName("heldKeys"), Nil, keys), r,
    call("storeAbout", v[BigInt](x), v[List[BigInt]](r)))
  private val x = step(1, "x", big)

  val inLoop: Prog[Stated[?]] = andThen(Prog.Loop(term([T[_]] => (s: Sym[T]) =>
    List.fill(3)(s.free[BigInt](key)).foldRight(s.nil[BigInt](big))(s.cons)), x,
    andThen(readAndStore(x), 2, call("put", v[BigInt](x)))), 3, call("clear"))

  private val e = step(4, "e", Ty.Str)
  val inHandler: Prog[Stated[?]] = andThen(Prog.Catch(andThen(call("put", v[BigInt](key)), 5, andThen(call("put",
    v[BigInt](key)), 6, Prog.Raise(term([T[_]] => (s: Sym[T]) => Lang(s).str("e"))))), Ty.Str, e,
    readAndStore(key)), 7, call("clear"))

  private val job = Ty.FnOf(List(big, keys), Ty.FlowOf(Ty.Unit, None))
  private val jobRuns = claim("jobRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("key", big)(k => l.forall[List[BigInt]]("rows", keys)(rs => l.forall[World]("before", Ty.World)(
      w => l.s.runs(l.call2(l.sym[BigInt => List[BigInt] => Program[Unit]]("expire", job), k, rs), w,
        Bound[Unit]("r", Ty.Unit), Bound[World]("after", Ty.World))((_, _) => l.truth))))))

  def kb(steps: Prog[Stated[?]]): Kb = Kb.of(claim("onePerKey")(each), assumption("rowsFromOutside")(each), heldOnce,
      jobRuns)
    .and(outside("tablesOneRun")(OutsideFact.Atomic(tables)), outside("heldOneRun")(OutsideFact.Atomic(held)),
      outside("heldByCode")(OutsideFact.OnlyCodeChanges(held)),
      outside("heldEmpty")(OutsideFact.Initially(held, DefName("heldEmpty"))))
    .modelling(database, heldModel)
    .declaring(_.copy(defines = List(rule("onePerKey")(nodup), rule("rowsFromOutside")(nodup), rule("heldOnce")(nodup),
      rule("heldEmpty")([T[_]] => (s: Sym[T], xs: T[List[BigInt]]) => s.eq(xs, s.nil[BigInt](big)))) ++
      flow("expireIt", List(key, rows), steps, Ty.Unit)))
    .naming(definition("expire", job))
    .coding(SymbolName("expire") -> Code.ProvenFlow(DefName("expireIt")))
    .linking(assumes("jobRuns", "tablesOneRun"), assumes("jobRuns", "heldOneRun"),
      assumes("jobRuns", "rowsFromOutside"),
      assumes("onePerKey", "rowsFromOutside"), assumes("heldOnce", "heldByCode"), assumes("heldOnce", "heldOneRun"),
      assumes("heldOnce", "heldEmpty"), assumes("heldOnce", "rowsFromOutside"))

  def resolved(steps: Prog[Stated[?]]): Resolved = Resolve(Validate(kb(steps).elaborated)
    .fold(ps => throw IllegalStateException(ps.toString), identity))
