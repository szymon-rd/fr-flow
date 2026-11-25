package frflow.dsl.compiled.normal

import frflow.core.effect.{ClassName, EType, FieldOf, MethodName, OutsideName, OutsideOf}
import frflow.core.normal.{Atom, Block as Statements, Local, Stmt}
import frflow.dsl.lifted.NotRead
import scala.collection.mutable
import scala.quoted.Quotes

/** What every part of the reading shares: the trees of the classes read (`q`), the names the program gives its
  * classes, fields and methods (said before any body is read, so that a body may name what is declared after
  * it), what it calls outside itself, in the order first met, and the method being read.
  */
private[normal] trait ReadBase:
  val q: Quotes
  import q.reflect.*
  given Quotes = q

  val classes: mutable.LinkedHashMap[Symbol, ClassName] = mutable.LinkedHashMap.empty
  val fields: mutable.LinkedHashMap[Symbol, FieldOf] = mutable.LinkedHashMap.empty
  val methods: mutable.LinkedHashMap[Symbol, MethodName] = mutable.LinkedHashMap.empty
  val outside: mutable.LinkedHashMap[Symbol, OutsideOf] = mutable.LinkedHashMap.empty
  /** The fields that are constants: a `final val` of a literal's type, which Scala reads as the literal. */
  val constants: mutable.Map[Symbol, Atom] = mutable.Map.empty

  /** Scala that is not read, with its place. */
  def refuse(what: String, at: Tree): Nothing =
    NotRead.raise(using q)(s"FrFlow: $what is not read into a tree of effects", Some(at))

  /** What the code does with the value of the expression being read: names it (`source`: the code's own name,
    * of a `val`; otherwise a name for an intermediate result), uses it unnamed, or drops it (a statement).
    */
  enum Use:
    case Named(name: String, source: Boolean)
    case Plain
    case Dropped

  /** One method being read: its locals, what each name of the code is bound to, and the statements of the
    * block being read, innermost first.
    */
  final class Body:
    private var last = 0
    private var open = List(mutable.ListBuffer.empty[Stmt])
    val bound: mutable.Map[Symbol, Atom] = mutable.Map.empty
    val vars: mutable.Map[Symbol, Local] = mutable.Map.empty
    val types: mutable.Map[Local, EType] = mutable.Map.empty

    def local(name: String, ty: EType): Local =
      last += 1
      val made = Local(name, last)
      types(made) = ty
      made

    def add(s: Stmt): Unit = open.head += s: Unit

    def isVar(l: Local): Boolean = vars.valuesIterator.contains(l)

    /** The statements added while `gives` is evaluated, as a block that gives what it gives. */
    def block(gives: => Atom): Statements =
      open = mutable.ListBuffer.empty[Stmt] :: open
      val value = gives
      val stmts = open.head.toList
      open = open.tail
      Statements(stmts, value)

  /** The name of something outside the code, given it when it is first called. */
  def outsideName(s: Symbol): OutsideName =
    val owner = s.owner.name.stripSuffix("$")
    val shared = outside.values.count(o => o.name.owner == owner && o.scala.endsWith("." + s.name))
    OutsideName(owner, if shared == 0 then s.name else s"${s.name}_${shared + 1}")
