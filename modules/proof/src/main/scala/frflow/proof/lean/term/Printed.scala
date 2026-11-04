package frflow.proof.lean.term

import frflow.core.expr.Binder
import frflow.core.name.SymbolName
import frflow.core.term.{Final, Stated}
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.{LBinder, LExpr}
import frflow.proof.lean.lower.{LowerEnv, LowerType, Naming}

/** A model's terms as Lean (`LeanTerm`), the one printer of terms: a formula (a claim's, an obligation's), a term
  * inside a program's step or a proposition (in the scope the step's variables are named in), and a define's inputs
  * and body, printed once as its `def`.
  */
object Printed:
  def formula[A](env: LowerEnv, naming: Naming)(t: Final[A]): LExpr = t[LeanTerm.S](LeanTerm(env))(Scope(0, naming))

  /** A node's claim as its `def claim` states it: every variable with what always holds of it (`Guarded`), and so each
    * value provided where the code runs that it mentions (`provided`), a value from outside (owner §21).
    */
  def claim(env: LowerEnv, naming: Naming, guards: List[Guard], provided: List[(SymbolName, Ty)])(
      t: Final[Boolean]): LExpr =
    formula(env, naming)(Guarded.ofProvided(Guarded.of(t, guards), guards, provided))

  /** A term over variables bound outside it: `depth` of them at levels, the rest steps, all named in `naming`. */
  def term(env: LowerEnv, naming: Naming, depth: Int)(t: Stated[?]): LExpr =
    standing(env, naming, depth, Map.empty)(t)

  /** The same, each of `by`'s values printed as what stands for it (a witness given before, in solving order). */
  def standing(env: LowerEnv, naming: Naming, depth: Int, by: Map[SymbolName, LExpr])(t: Stated[?]): LExpr =
    t.run[LeanTerm.S](LeanTerm(env, by))(Scope(depth, naming))

  def define[R](env: LowerEnv, naming: Naming)(inputs: List[Binder], body: Final[R]): (List[LBinder], LExpr) =
    val (names, scope) = Scope.over(inputs, naming)
    (names.zip(inputs).map((n, x) => LBinder.Explicit(n, LowerType(x.ty))), body[LeanTerm.S](LeanTerm(env))(scope))
