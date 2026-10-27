package frflow.proof.lean.lower

import cats.data.State
import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.proof.lean.ast.*

/** The names taken in one Lean expression, by owner: a variable's name is unique in it and none of the reserved
  * names or of the domain types (nor a prefix of one). Threaded through the lowering as `State[Naming, _]`.
  * `canonical`: every variable named `x`, numbered in the order bound, whatever the Scala called it, so a term
  * prints the same however its variables were named (what a node's content says its formula means).
  */
final case class Naming(taken: Map[String, NameOwner], variables: Map[VarId, LeanName], reserved: Set[String],
    types: Set[String], helpers: Int, canonical: Boolean = false)

object Naming:
  def over(reserved: Set[String], types: Set[String]): Naming = Naming(Map.empty, Map.empty, reserved, types, 0)

  /** The variable's name: its hint (`x` when canonical), or the first free `hint_1`, `hint_2`, … */
  def bind(x: Binder): State[Naming, LeanName] = bindAvoiding(x, Set.empty)

  /** As `bind`, and none of `avoid` (`∀ x ∈ r, …` puts `r` in the scope of `x`). */
  def bindAvoiding(x: Binder, avoid: Set[String]): State[Naming, LeanName] = State { n =>
    val chosen = first(n, Names.ident(if n.canonical then "x" else x.hint), NameOwner.Variable(x.id), avoid)
    val taken = n.taken.updated(chosen.text, NameOwner.Variable(x.id))
    (n.copy(taken = taken, variables = n.variables.updated(x.id, chosen)),
      chosen)
  }

  /** A helper variable the lowering needs (`k`, `y`), avoiding the names in `avoid` (those of the receiver). */
  def helper(base: String, avoid: Set[String]): State[Naming, LeanName] = State { n =>
    val owner = NameOwner.Helper(n.helpers)
    val chosen = first(n, Names.builtin(base), owner, avoid)
    (n.copy(taken = n.taken.updated(chosen.text, owner), helpers = n.helpers + 1), chosen)
  }

  /** The name bound to a variable. Unbound is a FrFlow bug: elaboration builds every term in its binders' scope. */
  def of(x: Binder): State[Naming, LeanName] = State.inspect(_.variables.getOrElse(x.id,
    throw IllegalStateException(s"FrFlow bug: variable ${x.hint} (${x.id.value}) lowered outside its binder")))

  private def first(n: Naming, base: LeanName, owner: NameOwner, avoid: Set[String]): LeanName =
    // An escaped keyword numbered is a plain name (`by_1`): `«by»_1` is not one.
    val stem = base.text.stripPrefix("«").stripSuffix("»")
    (Iterator(base.text) ++ Iterator.from(1).map(i => s"${stem}_$i")).find { c =>
      n.taken.get(c).forall(_ == owner) && !n.reserved(c) && !avoid(c) &&
        !n.types.exists(t => t == c || t.startsWith(c + "."))
    }.map(LeanName.unsafe).getOrElse(base) // the candidates never end
