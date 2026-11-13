package frflow.proof.prover.term

import frflow.core.expr.Binder
import frflow.core.name.SymbolName
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.term.language.{Final, Stated}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.{Binding, Syntax}
import frflow.proof.prover.lower.{LowerEnv, LowerType, Naming, Seen}

/** A model's terms written for the prover (`ProverTerm`), into the syntax asked for (`E`): a formula (a claim's,
  * an obligation's), a term inside a program's step or a proposition (in the scope the step's variables are named
  * in), and a define's inputs and body, printed once as its `def`.
  */
object Printed:
  def formula[E: Syntax: Seen, A](env: LowerEnv, naming: Naming)(t: Final[A]): E =
    t[ProverTerm.S[E]](ProverTerm[E](env))(Scope(0, naming))

  /** A node's claim as its `def claim` states it: every variable with what always holds of it (`Guarded`), and so each
    * value provided where the code runs that it mentions (`provided`), a value from outside (owner §21).
    */
  def claim[E: Syntax: Seen](env: LowerEnv, naming: Naming, guards: List[Guard], provided: List[(SymbolName, Ty)])(
      t: Final[Boolean]): E =
    formula[E, Boolean](env, naming)(Guarded.ofProvided(Guarded.of(t, guards), guards, provided))

  /** A term over variables bound outside it: `depth` of them at levels, the rest steps, all named in `naming`. */
  def term[E: Syntax: Seen](env: LowerEnv, naming: Naming, depth: Int)(t: Stated[?]): E =
    standing[E](env, naming, depth, Map.empty)(t)

  /** The same, each of `by`'s values printed as what stands for it (a witness given before, in solving order). */
  def standing[E: Syntax: Seen](env: LowerEnv, naming: Naming, depth: Int, by: Map[SymbolName, E])(t: Stated[?]): E =
    t.run[ProverTerm.S[E]](ProverTerm[E](env, by))(Scope(depth, naming))

  def define[E: Syntax: Seen, R](env: LowerEnv, naming: Naming)(inputs: List[Binder], body: Final[R])
      : (List[Binding[E]], E) =
    val (names, scope) = Scope.over(inputs, naming)
    val types = new LowerType(summon[Syntax[E]])
    (names.zip(inputs).map((n, x) => Binding.Explicit(n, types(x.ty))),
      body[ProverTerm.S[E]](ProverTerm[E](env))(scope))
