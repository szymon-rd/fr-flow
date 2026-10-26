package crm

import frflow.*
import frflow.core.code.Values
import frflow.core.expr.{Binder, Expr}
import frflow.core.name.{KbName, ModelName, SymbolName, VarId}
import frflow.core.term.{Program, World}
import frflow.core.ty.{NumKind, Ty}
import frflow.eval.{Env, ScalaValue}
import frflow.eval.term.Evaluate
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed

/** A run of a program from a world (`Worlds.runs`, `fails`) under each interpreter: evaluated by running the program
  * on the world, printed as Lean taking the run's pair apart, and in the IR a binder of the outcome and the world
  * after.
  */
class RunsSuite extends munit.FunSuite:
  private val (n, w) = (Binder(VarId.level(0), "now", Ty.Num(NumKind.Big)), Binder(VarId.level(1), "before", Ty.World))
  private val (now, before) = (Term.free[BigInt](n), Term.free[World](w))
  private val tables = Tables(CrmStore(List(1, 2)), Nil)
  private val world = World.of(Map(ModelName("databaseModel") -> tables))

  private val kept = runExpiry(now).from(before) { (result, after) => result === databaseModel.in(after).store }
  private val failed = runExpiry(now).from(before).failing { (error: Term[String], after) =>
    error === "down" && databaseModel.in(after).store === databaseModel.in(before).store }

  private def env(run: BigInt => Program[CrmStore]): Env =
    Env.of(Values.none).withSymbol(SymbolName("runExpiry"), ScalaValue(run))
      .bind(n.id, ScalaValue(BigInt(5))).bind(w.id, ScalaValue(world))

  test("evaluated: the program run on the world before, the post of its result and the world after") {
    val keeps = env(_ => Program.of(v => (Right(tables.store), v)))
    val drops = env(_ => Program.of(v => (Right(CrmStore(Nil)), v)))
    assertEquals((Evaluate.of(kept.run)(keeps), Evaluate.of(kept.run)(drops)), (Right(true), Right(false)))
  }

  test("evaluated: a run that fails meets every success post, and a failure post is of its error") {
    val down = env(_ => Program.of(v => (Left("down"), v)))
    assertEquals((Evaluate.of(kept.run)(down), Evaluate.of(failed.run)(down)), (Right(true), Right(true)))
  }

  test("printed: the run's pair taken apart by a match, its names the developer's") {
    val lean = LowerEnv(KbName("Crm"), _ => Nil, _ => Names.builtin("database"), _ => Names.builtin("Database"),
      _ => None)
    val (_, body) = Printed.define(lean, Naming.over(Set("runExpiry"), Set("CrmStore")))(List(n, w), kept.run)
    assertEquals(Print.expr(body),
      "(match (runExpiry now before) with | (result, after) => (result = after.database.store))")
  }

  test("in the IR: a run binds its outcome and the world after, past the variables around it") {
    kept.exprAt(2) match
      case Expr.Runs(_, Expr.Var(`w`), false, o, a, _) => assertEquals((o.id, a.id), (VarId.level(2), VarId.level(3)))
      case other                                     => fail(other.toString)
  }
