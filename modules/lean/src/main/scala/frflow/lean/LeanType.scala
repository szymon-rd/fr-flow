package frflow
package lean

/** A Lean type, read back from its text. */
enum LeanType:
  case Name(n: String)
  case ListOf(t: LeanType)
  case OptionOf(t: LeanType)
  case Prod(a: LeanType, b: LeanType)
  case Fun(text: String)

object LeanType:
  /** The depth of parentheses after each character of `t`. */
  private def depths(t: String): IndexedSeq[Int] =
    t.scanLeft(0)((d, c) => if c == '(' then d + 1 else if c == ')' then d - 1 else d).tail

  /** Where `sym` first occurs in `t` outside parentheses. */
  private def atTop(t: String, sym: String): Option[Int] =
    val d = depths(t)
    t.indices.find(i => d(i) == 0 && t.startsWith(sym, i))

  /** Whether `t` is wrapped in one pair of parentheses. */
  private def wrapped(t: String): Boolean = t.startsWith("(") && depths(t).indexWhere(_ == 0) == t.length - 1

  def parse(t0: String): LeanType =
    val t = t0.trim
    if wrapped(t) then parse(t.substring(1, t.length - 1))
    else if atTop(t, "→").isDefined then Fun(t)
    else atTop(t, "×") match
      case Some(i)                         => Prod(parse(t.take(i)), parse(t.drop(i + 1)))
      case None if t.startsWith("List ")   => ListOf(parse(t.drop(5)))
      case None if t.startsWith("Option ") => OptionOf(parse(t.drop(7)))
      case None                            => Name(t)

  /** The top-level arrows of a Lean type: `A → (B → C) → D` is `A`, `(B → C)`, `D`. */
  def arrows(t0: String): List[String] =
    val x = t0.trim
    val t = if x.startsWith("(") && x.endsWith(")") && (0 +: depths(x.init.tail)).forall(_ >= 0) then x.init.tail.trim else x
    val d = depths(t)
    val cuts = t.indices.filter(i => d(i) == 0 && t.startsWith(" → ", i)).toList
    (0 :: cuts.map(_ + 3)).zip(cuts :+ t.length).map((from, to) => t.substring(from, to).trim)

  /** Doing nothing, for an operation of type `t`: returning `[]`, `none`, `False`, or an input unchanged. */
  def nothing(t: String): Option[String] =
    val ps = arrows(t)
    val r = ps.last
    val ins = ps.init
    val v = if ins.isEmpty then None
      else if r == "Prop" then Some("False")
      else if r.startsWith("(List ") || r.startsWith("List ") then Some("[]")
      else if r.startsWith("(Option ") || r.startsWith("Option ") then Some("none")
      else ins.indexOf(r) match { case -1 => None; case i => Some(s"x$i") }
    v.map(b => s"(fun ${ins.indices.map(i => s"(x$i : ${ins(i)})").mkString(" ")} => $b)")
