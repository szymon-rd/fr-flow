package frflow.proof.lean.lower

import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.vocab.{DefineForm, Vocabulary}
import frflow.proof.lean.ast.*

/** A race's winner as Lean reads it (`Prog.leftWins`): the scheduler's choice, `FrFlow.Races.leftWins`, which a
  * program racing two branches asks of its monad. On `StateM World` it is the next of the world's `races` (`true`:
  * the left wins; the left when none is left, as the Scala tests' sequential runs read it), the field the World has
  * when some program races; on `ExceptT E (StateM World)` it is lifted (the library's instance).
  */
object LowerRaces:
  import Atoms.{const, name}

  val leftWins: LExpr = const("FrFlow.Races.leftWins")
  /** The world's field of the races' winners, which no model's field takes (`Reserved`). */
  val field: LeanName = Names.builtin("races")

  /** Whether some program of the vocabulary races two branches. */
  def racing(v: Vocabulary): Boolean = v.defines.filter(_.form == DefineForm.Flow).exists(d => d.lambda.body match
    case Expr.Do(p, _) => races(p)
    case _             => false)

  def races[E](p: Prog[E]): Boolean = Progs.operations(p).contains(Prog.leftWins)

  /** `[FrFlow.Races m]`: what a program racing asks of its monad `m`. */
  def binder(m: LeanName): LBinder = LBinder.Instance(LExpr.App(const("FrFlow.Races"), List(LExpr.Name(m))))

  /** The instance on `StateM World`, and its lemma for `frflow_defs`. */
  def decls: List[Decl] =
    val (w, s) = (Names.builtin("w"), Names.builtin("s"))
    val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), field.text))
    val put = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), LExpr.Update(LExpr.Name(w), List(field ->
      LExpr.Name(s))))
    val next = LExpr.App(const("FrFlow.nextRace"), List(LExpr.Paren(get), LExpr.Paren(put)))
    val monad = LExpr.App(name("StateM"), List(name("World")))
    List(Decl.Instance(LExpr.App(const("FrFlow.Races"), List(LExpr.Paren(monad))),
        List(InstanceField(Names.ident("leftWins"), Nil, next))),
      Decl.Theorem(List(Attr.FrflowDefs), Names.builtin("FrFlow.Races.leftWins_onWorld"), Nil,
        LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(leftWins), LExpr.App(monad, List(name("Bool")))), next),
        Proof.Rfl, Break.NextLine))
