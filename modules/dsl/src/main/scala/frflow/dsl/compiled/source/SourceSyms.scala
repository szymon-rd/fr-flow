package frflow.dsl.compiled.source

import frflow.core.threads.Datum
import frflow.core.threads.Datum.{Nat, Text, Truth, Whole}
import scala.collection.mutable
import scala.quoted.Quotes

/** How a definition is named in the tree read (`FrFlow/Scala/Tree.v`, `sym`): one a class or a package declares,
  * by its owner, its name and its signature (`Member`); one made inside a method, by its name and a number, the
  * order it is first met in (`Local`), since two of a method may share a name. A class made inside a method is
  * named with its number too. And a constant, and a definition's flags and annotations.
  */
private[source] trait SourceSyms:
  val q: Quotes
  import q.reflect.*

  private val numbered = mutable.HashMap.empty[Symbol, Int]
  private def number(s: Symbol): Int = numbered.getOrElseUpdate(s, numbered.size)

  private def owners(s: Symbol): Iterator[Symbol] = Iterator.iterate(s)(_.maybeOwner).takeWhile(!_.isNoSymbol)
  private def isLocal(s: Symbol): Boolean = !s.maybeOwner.isNoSymbol && s.maybeOwner.isTerm

  /** A class by its full name; one made inside a method, with its number. */
  def classKey(cls: Symbol): String =
    if owners(cls).drop(1).exists(_.isTerm) then s"${cls.fullName}#${number(cls)}" else cls.fullName

  /** What declares `s`: a class by its key, anything else by its full name. */
  def scopeKey(s: Symbol): String = if s.isClassDef then classKey(s) else s.fullName

  def sym(s: Symbol): Datum =
    if s.isNoSymbol then Datum.of("NoSym")
    else if isLocal(s) then Datum.of("Local", Text(s.name), Nat(number(s)))
    else Datum.of("Member", Text(scopeKey(s.maybeOwner)), Text(s.name), Text(signature(s)))

  /** What tells a method from the others of its name: the erased types of its parameters and its result. A
    * package says it is one: it is no definition of the code read.
    */
  private def signature(s: Symbol): String =
    if s.isDefDef then s"${s.signature.paramSigs.mkString(",")}:${s.signature.resultSig}"
    else if s.isPackageDef then "package" else ""

  /** A definition's flags, as the compiler names them, then its annotations' classes. */
  def flags(s: Symbol): Datum = Datum.texts(
    s.flags.show.split('|').toList.map(_.trim.stripPrefix("Flags.")).filter(_.nonEmpty) ++
      s.annotations.map(a => s"@${a.tpe.typeSymbol.fullName}"))

  def const(c: Constant): Datum = c match
    case UnitConstant()     => Datum.of("CUnit")
    case NullConstant()     => Datum.of("CNull")
    case BooleanConstant(b) => Datum.of("CBool", Truth(b))
    case ByteConstant(b)    => Datum.of("CByte", Whole(BigInt(b)))
    case ShortConstant(s)   => Datum.of("CShort", Whole(BigInt(s)))
    case CharConstant(c)    => Datum.of("CChar", Whole(BigInt(c.toInt)))
    case IntConstant(i)     => Datum.of("CInt", Whole(BigInt(i)))
    case LongConstant(l)    => Datum.of("CLong", Whole(BigInt(l)))
    case FloatConstant(f)   => Datum.of("CFloat", Text(f.toString))
    case DoubleConstant(d)  => Datum.of("CDouble", Text(d.toString))
    case StringConstant(s)  => Datum.of("CString", Text(s))
    case ClassOfConstant(t) => Datum.of("CClassOf", Text(t.show))
