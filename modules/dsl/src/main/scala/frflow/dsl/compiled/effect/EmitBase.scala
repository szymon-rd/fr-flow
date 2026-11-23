package frflow.dsl.compiled.effect

import frflow.core.effect.{ClassName, FieldOf, Idents, MethodName, OutsideName, OutsideOf, Pure}
import frflow.dsl.lifted.NotRead
import scala.collection.mutable
import scala.quoted.Quotes

/** What every part of the emitter shares: the trees of the classes read (`q`), the names the program gives its
  * classes, fields and methods (said before any body is read, so that a body may name what is declared after
  * it), what it calls outside itself, in the order first met, and the names a method's tree has bound.
  */
private[effect] trait EmitBase:
  val q: Quotes
  import q.reflect.*
  given Quotes = q

  val classes: mutable.LinkedHashMap[Symbol, ClassName] = mutable.LinkedHashMap.empty
  val fields: mutable.LinkedHashMap[Symbol, FieldOf] = mutable.LinkedHashMap.empty
  val methods: mutable.LinkedHashMap[Symbol, MethodName] = mutable.LinkedHashMap.empty
  val outside: mutable.LinkedHashMap[Symbol, OutsideOf] = mutable.LinkedHashMap.empty
  /** The fields that are constants: a `final val` of a literal's type, which Scala reads as the literal. */
  val constants: mutable.Map[Symbol, Pure] = mutable.Map.empty

  /** Scala the emitter does not read, with its place. */
  def refuse(what: String, at: Tree): Nothing =
    NotRead.raise(using q)(s"FrFlow: $what is not read into a tree of effects", Some(at))

  /** The names bound in one method's tree: each is bound once, so that no binding hides another. */
  final class Fresh:
    private val used = mutable.Set.empty[String]

    def apply(base: String): String =
      val name = Idents.local(base)
      val free = Iterator(name) ++ Iterator.from(1).map(i => s"$name$i")
      val chosen = free.find(n => !used(n)).get
      used += chosen
      chosen

  /** Where an expression is read: the object the method is called on, the value each variable in scope has now
    * (a `var`'s is its last one), which of them are `var`s, the method's names; and what is done with the
    * expression's value: the name the code gives it, if it gives one (`val total = …`), which it then has in
    * the tree, or that the code drops it (a statement). What follows an expression is read in a place that says
    * neither (`plain`).
    */
  final case class Env(self: Pure, values: Map[Symbol, Pure], vars: Set[Symbol], fresh: Fresh,
      hint: Option[String] = None, dropped: Boolean = false):
    def plain: Env = copy(hint = None, dropped = false)
    def hinted(name: Option[String]): Env = copy(hint = name, dropped = false)
    def dropping: Env = copy(hint = None, dropped = true)
    /** This place, with what is done with the value as `other` says. */
    def like(other: Env): Env = copy(hint = other.hint, dropped = other.dropped)
    /** A name not bound yet: the one the code gives the value, or `otherwise`. */
    def name(otherwise: String): String = fresh(hint.getOrElse(otherwise))
    def having(s: Symbol, value: Pure): Env = copy(values = values + (s -> value))
    def havingAll(of: List[(Symbol, Pure)]): Env = copy(values = values ++ of)
    def declaring(s: Symbol, value: Pure): Env =
      having(s, value).copy(vars = if s.flags.is(Flags.Mutable) then vars + s else vars)

  /** The name of something outside the code, given it when it is first called. */
  def outsideName(s: Symbol): OutsideName =
    val owner = s.owner.name.stripSuffix("$")
    val shared = outside.values.count(o => o.name.owner == owner && o.scala.endsWith("." + s.name))
    OutsideName(owner, if shared == 0 then s.name else s"${s.name}_${shared + 1}")
