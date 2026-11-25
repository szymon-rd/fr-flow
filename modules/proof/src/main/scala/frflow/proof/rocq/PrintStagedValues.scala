package frflow.proof.rocq

import frflow.core.code.Datum
import frflow.core.code.Datum.{Of, Text, Truth, Whole}
import frflow.core.staged.{Arg, Kept, Sym, V}

/** A value and an argument of staged code as Rocq terms. A function's definition, its unit's name in the place
  * of its body, is written once, under a name (`stubs`), and named where a value holds it.
  */
final class PrintStagedValues(stubs: Map[Datum, String]):
  private def text(s: String): String = "\"" + s.replace("\"", "\"\"") + "\""

  def sym(s: Sym): String = s match
    case Sym.Member(o, n, sig) => s"(Member ${text(o)} ${text(n)} ${text(sig)})"
    case Sym.Local(n, id)      => s"(Local ${text(n)} $id)"
    case Sym.NoSym             => "NoSym"

  /** A constant as the value the code writes (`Value.of_const`). */
  private def constant(c: Datum): String = c match
    case Of("CNull", _)                                            => "vnull"
    case Of("CBool", List(Truth(b)))                               => s"(VBool $b)"
    case Of("CByte" | "CShort" | "CChar" | "CInt", List(Whole(z))) => s"(vint ($z)%Z)"
    case Of("CLong", List(Whole(z)))                               => s"(vlong ($z)%Z)"
    case Of("CString", List(Text(s)))                              => s"(vstr ${text(s)})"
    case Of("CClassOf", List(Text(n)))                             => s"(VObj (ClassOf ${text(n)}))"
    case other                                                     =>
      throw IllegalArgumentException(s"FrFlow bug: no value of $other")

  def kept(k: Kept): String =
    val entries = k.entries.map((key, v) => s"(${text(key)}, ${value(v)})").mkString("[", "; ", "]")
    k.rest.fold(entries)(sc => if k.entries.isEmpty then sc else s"($entries ++ $sc)%list")

  def value(v: V): String = v match
    case V.Var(x)             => x
    case V.Const(c)           => constant(c)
    case V.Unit               => "VUnit"
    case V.Module(n)          => s"(VObj (Module ${text(n)}))"
    case V.Many(vs)           => vs.map(value).mkString("(VList [", "; ", "])")
    case V.Function(stub, k)  => s"(VCode (Fn ${stubs(stub)} ${kept(k)} []))"
    case V.ByName(unit, k)    => s"(VCode (Thunk (Ident ${sym(unit)}) ${kept(k)}))"
    case V.Found(sc, key)     => s"(Staged.found $sc ${text(key)})"

  private def ty(t: Datum): String = PrintData(t, 0).linesIterator.map(_.trim).mkString(" ")

  /** An argument that is no program, on one line. */
  def simple(a: Arg): String = a match
    case Arg.Val(v)    => value(v)
    case Arg.Vals(vs)  => vs.map(value).mkString("[", "; ", "]")
    case Arg.Text(s)   => text(s)
    case Arg.Name(s)   => sym(s)
    case Arg.Type(t)   => ty(t)
    case Arg.Types(ts) => ts.map(ty).mkString("[", "; ", "]")
    case Arg.Count(n)  => n.toString
    case Arg.Scope(k)  => kept(k)
    case other         => throw IllegalArgumentException(s"FrFlow bug: no simple argument in $other")
