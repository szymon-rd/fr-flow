package frflow.proof.effect

import frflow.core.effect.{Effect, Pure, Tree}

/** A tree as Rocq writes it with the notations of `FrFlow/Effect/Tree.v`: one effect a line, what it gave named
  * before `<-`; a choice and a loop's body two columns in.
  */
object PrintTree:
  def apply(t: Tree): List[String] = t match
    case Tree.Give(p)                  => List(s"ret ${PrintPure.arg(p)}")
    case Tree.Do(Some(x), e, next)     => s"$x <- ${effect(e)} ;;" :: apply(next)
    case Tree.Do(None, e, next)        => s"${effect(e)} ;;;" :: apply(next)
    case Tree.Name(x, p, next)         => s"let $x := ${PrintPure(p)} in" :: apply(next)
    case Tree.Branch(c, yes, no)       => (s"if ${PrintPure(c)} then" :: in(apply(yes))) ++ ("else" :: in(apply(no)))
    case Tree.After(first, Nil, next)  => around("(", apply(first), ") ;;;") ++ apply(next)
    case Tree.After(first, xs, next)   => around(s"${pattern(xs)} <- (", apply(first), ") ;;") ++ apply(next)
    case Tree.Loop(s, start, body, next) =>
      around(s"${pattern(s)} <- loop (fun ${pattern(s)} =>", "" :: apply(body), s") ${state(start)} ;;") ++ apply(next)
    case Tree.Again(s)                 => List(s"again ${state(s)}")
    case Tree.Leave(s)                 => List(s"leave ${state(s)}")

  /** What several values are named by, as a binder: one name, a pattern of several, or nothing to name. */
  private def pattern(names: List[String]): String = names match
    case Nil        => "_"
    case one :: Nil => one
    case several    => several.mkString("'(", ", ", ")")

  private def state(values: List[Pure]): String = PrintPure.arg(Pure.Several(values))

  private def in(lines: List[String]): List[String] = lines.map("  " + _)

  /** `lines` between `open` and `close`: the first after `open`, the others four columns in. */
  private def around(open: String, lines: List[String], close: String): List[String] =
    val inner = (open + lines.head) :: lines.tail.map("    " + _)
    inner.init :+ (inner.last + close)

  private def effect(e: Effect): String = e match
    case Effect.Get(on, f)        => s"get ${PrintPure.arg(on)} ${Named.field(f)}"
    case Effect.Put(on, f, v)     => s"put ${PrintPure.arg(on)} ${Named.field(f)} ${PrintPure.arg(v)}"
    case Effect.New(c)            => s"new ${Named.cls(c)}"
    case Effect.Call(m, on, to)   => s"call ${PrintPure.arg(on)} ${Named.method(m)} ${state(to)}"
    case Effect.Ext(m, to)        => s"ext ${Named.outside(m)} ${state(to)}"
