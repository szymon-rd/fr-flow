package frflow.proof.lean.term

import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.ty.Ty
import frflow.proof.lean.ast.{LeanName, Names}
import frflow.proof.lean.lower.Naming

/** The context the Lean printer passes down a term (LNCS 7470 §2.4: a context-passing interpreter, there the
  * polarity of push-negation, here the binders around the term): how many there are, and the names taken (`Naming`:
  * the binders', the free variables', and the reserved ones). A binder is named by its hint, or, when that is taken,
  * by the hint and the first number not taken (`x_1`); never by a name its receiver mentions.
  */
final case class Scope(depth: Int, naming: Naming):
  /** The name of a binder with this hint here, avoiding `avoid`, and the scope of its body. */
  def bind(hint: String, ty: Ty, avoid: Set[String] = Set.empty): (LeanName, Scope) =
    val (n, name) = Naming.bindAvoiding(Binder(VarId.level(depth), hint, ty), avoid).run(naming).value
    (name, Scope(depth + 1, n))

  /** A variable bound outside the term (a define's input, a program's step): its name, else its hint. */
  def named(x: Binder): LeanName = naming.variables.getOrElse(x.id, Names.ident(x.hint))

object Scope:
  /** The scope of a term over the given inputs (bound outside it, at levels `0 … n-1`). */
  def over(inputs: List[Binder], naming: Naming): (List[LeanName], Scope) =
    val (n, names) = inputs.traverse(Naming.bind).run(naming).value
    (names, Scope(inputs.size, n))
