package frflow.dsl.compiled.effect

import frflow.core.effect.{Idents, Pure, Tree as Emitted}
import frflow.core.normal.{Atom, Local}
import scala.collection.mutable

/** The names bound in one method's tree: each is bound once, so that no binding hides another. */
private[effect] final class Fresh:
  private val used = mutable.Set.empty[String]

  def apply(base: String): String =
    val name = Idents.local(base)
    val free = Iterator(name) ++ Iterator.from(1).map(i => s"$name$i")
    val chosen = free.find(n => !used(n)).get
    used += chosen
    chosen

/** Where a statement is evaluated: the object the method is called on, the value each local has now (a `var`'s
  * is its last one), which locals are `var`s, and the method's names.
  */
private[effect] final case class Env(self: Pure, values: Map[Local, Pure], vars: Set[Local], fresh: Fresh):
  def having(l: Local, value: Pure): Env = copy(values = values + (l -> value))
  def havingAll(of: List[(Local, Pure)]): Env = copy(values = values ++ of)
  def declaring(l: Local, value: Pure): Env = having(l, value).copy(vars = vars + l)

  /** An atom's value: evaluating one does nothing. */
  def pure(a: Atom): Pure = a match
    case Atom.Of(l)    => values(l)
    case Atom.Whole(n) => Pure.Whole(n)
    case Atom.Truth(b) => Pure.Truth(b)
    case Atom.Nothing  => Pure.Nothing
    case Atom.NoObject => Pure.NoObject
    case Atom.Self     => self

private[effect] object Env:
  /** `value` under a name of its own, unless writing it again costs nothing. */
  def named(value: Pure, base: String, env: Env)(next: Pure => Emitted): Emitted =
    if value.atomic then next(value)
    else
      val name = env.fresh(base)
      Emitted.Name(name, value, next(Pure.Local(name)))
