package frflow.proof.layout.calls

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.expr.{OutsideFact, Prog, Value}
import frflow.core.name.{DefName, ModelName, SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, ModelOp, StateModel}
import frflow.proof.layout.Fixture.*

/** A crm-shaped database whose tables hold one row per key (owner §37, §40): `storeAbout(key, rows)` hands the rows
  * it is given to the database's plain Scala, and `onePerKey` says each list of keys holds each key once. The job
  * adds a key to the rows it is given only when they do not hold it, so what it hands `storeAbout` meets the rule
  * on every path (`made_expireIt_call_0`); the seeded bug adds it whether or not they do, so a run storing a
  * duplicate breaks it, and Lean does not prove it.
  */
object Rows:
  private val big = Lang.big
  private val keys = Ty.ListOf(big)
  private val tables = ModelName("tables")
  private val (key, rows) = (at(0, "key", big), at(1, "rows", keys))
  private val unit: Stated[Unit] = term([T[_]] => (s: Sym[T]) => s.lit((), Value.Unit, Ty.Unit))
  private val model = StateModel(tables, "the database's tables: how many rows they hold", big, List(
    ModelOp(SymbolName("storeAbout"), List(key, rows), Ty.Unit, Prog.Write(tables,
      term([T[_]] => (s: Sym[T]) => s.length(s.free[List[BigInt]](rows)))))), None)

  private val held = at(0, "rows", keys)
  /** The rule, a define named as each statement of it. */
  private def rule(name: String) = Define(DefName(name), Written.lambda(List(held), [T[_]] => (s: Sym[T]) =>
    s.nodup(s.free[List[BigInt]](held)), SourceText(name)), DefineForm.Function)
  private val each = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[List[BigInt]]("rows", keys))(x => l.s.nodup(x)))
  val onePerKey: frflow.core.spec.Node = claim("onePerKey")(each)
  /** What the job is given from outside holds each key once too (owner §21). */
  private val rowsFromOutside = assumption("rowsFromOutside")(each)

  /** The rows with the key added at the end. */
  private val added: Stated[List[BigInt]] = term([T[_]] => (s: Sym[T]) => s.append(s.free[List[BigInt]](rows),
    s.cons(s.free[BigInt](key), s.nil[BigInt](big))))
  private val store = Prog.Call(SymbolName("storeAbout"), List(v[BigInt](key), added), Ty.Unit)
  /** The key added only when the rows do not hold it. */
  val once: Prog[Stated[?]] = Prog.Branch(term([T[_]] => (s: Sym[T]) =>
    s.contains(s.free[List[BigInt]](rows), s.free[BigInt](key))), Prog.Pure(unit), store)

  private val job = Ty.FnOf(List(big, keys), Ty.FlowOf(Ty.Unit, None))
  private val jobRuns = claim("jobRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("key", big)(k => l.forall[List[BigInt]]("rows", keys)(rs => l.forall[World]("before", Ty.World)(
      w => l.s.runs(l.call2(l.sym[BigInt => List[BigInt] => Program[Unit]]("expire", job), k, rs), w,
        Bound[Unit]("r", Ty.Unit), Bound[World]("after", Ty.World))((_, _) => l.truth))))))

  /** The theory with the job's steps `steps`: `once`, or the seeded bug, the store called whatever the rows hold. */
  def kb(steps: Prog[Stated[?]]): Kb = Kb.of(onePerKey, rowsFromOutside, jobRuns)
    .and(outside("tablesOneRun")(OutsideFact.Atomic(tables)))
    .modelling(model)
    .declaring(_.copy(defines = rule("onePerKey") :: rule("rowsFromOutside") ::
      flow("expireIt", List(key, rows), steps, Ty.Unit)))
    .naming(definition("expire", job))
    .coding(SymbolName("expire") -> Code.ProvenFlow(DefName("expireIt")))
    .linking(assumes("jobRuns", "tablesOneRun"), assumes("jobRuns", "rowsFromOutside"),
      assumes("onePerKey", "rowsFromOutside"))

  def resolved(steps: Prog[Stated[?]]): Resolved = Resolve(Validate(kb(steps).elaborated)
    .fold(ps => throw IllegalStateException(ps.toString), identity))

  /** What `once` does, the duplicate stored. */
  val duplicates: Prog[Stated[?]] = store

  private val (r, x) = (step(0, "r", keys), step(1, "x", keys))
  /** The duplicate stored through a branch's result: the rows with the key added, whichever way it goes. */
  val viaBranch: Prog[Stated[?]] = Prog.Bind(Prog.Branch(term([T[_]] => (s: Sym[T]) =>
    s.contains(s.free[List[BigInt]](rows), s.free[BigInt](key))), Prog.Pure(added), Prog.Pure(added)), r,
    Prog.Call(SymbolName("storeAbout"), List(v[BigInt](key), v[List[BigInt]](r)), Ty.Unit))
  /** The duplicate stored through a loop over a list the job builds: the rows with the key added, alone. */
  val viaLoop: Prog[Stated[?]] = Prog.Loop(term([T[_]] => (s: Sym[T]) =>
    s.cons(added.run[T](s), s.nil[List[BigInt]](keys))), x,
    Prog.Call(SymbolName("storeAbout"), List(v[BigInt](key), v[List[BigInt]](x)), Ty.Unit))
