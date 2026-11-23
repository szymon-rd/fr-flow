package frflow.proof.effect

import frflow.core.effect.{EType, Prim, Pure}

/** A pure expression of a tree, and a type, as Rocq terms. Numbers are `Z`, an operation on them the JVM's
  * (`FrFlow/Effect/Int32.v`).
  */
object PrintPure:
  /** The expression where a function's argument stands: in parentheses unless it is a name or a constant. */
  def arg(p: Pure): String = p match
    case Pure.Whole(n) if n < 0   => s"($n)"
    case Pure.Several(one :: Nil) => arg(one)
    case Pure.Several(_)          => apply(p)
    case _ if p.atomic            => apply(p)
    case _                        => s"(${apply(p)})"

  def apply(p: Pure): String = p match
    case Pure.Local(name)         => name
    case Pure.Whole(n)            => n.toString
    case Pure.Truth(b)            => b.toString
    case Pure.Nothing             => "tt"
    case Pure.NoObject            => "null"
    case Pure.Applied(op, to)     => applied(op, to.map(arg))
    case Pure.Choice(c, yes, no)  => s"if ${apply(c)} then ${apply(yes)} else ${apply(no)}"
    case Pure.Several(Nil)        => "tt"
    case Pure.Several(one :: Nil) => apply(one)
    case Pure.Several(of)         => of.map(apply).mkString("(", ", ", ")")

  private def applied(op: Prim, to: List[String]): String = (op, to) match
    case (Prim.Add, List(a, b))      => s"iadd $a $b"
    case (Prim.Sub, List(a, b))      => s"isub $a $b"
    case (Prim.Mul, List(a, b))      => s"imul $a $b"
    case (Prim.Neg, List(a))         => s"ineg $a"
    case (Prim.Less, List(a, b))     => s"$a <? $b"
    case (Prim.LessEq, List(a, b))   => s"$a <=? $b"
    case (Prim.More, List(a, b))     => s"$a >? $b"
    case (Prim.MoreEq, List(a, b))   => s"$a >=? $b"
    case (Prim.SameInt, List(a, b))  => s"$a =? $b"
    case (Prim.And, List(a, b))      => s"andb $a $b"
    case (Prim.Or, List(a, b))       => s"orb $a $b"
    case (Prim.Not, List(a))         => s"negb $a"
    case (Prim.SameBool, List(a, b)) => s"Bool.eqb $a $b"
    case (Prim.SameRef, List(a, b))  => s"same $a $b"
    case _                           => throw IllegalArgumentException(s"FrFlow bug: $op applied to ${to.size}")

  def ty(t: EType): String = t match
    case EType.Int                => "Z"
    case EType.Bool               => "bool"
    case EType.Unit               => "unit"
    case EType.Ref                => "ref"
    case EType.Several(Nil)       => "unit"
    case EType.Several(one :: Nil) => ty(one)
    case EType.Several(of)        => of.map(ty).mkString("(", " * ", ")%type")

  /** What a field of the type holds before it is written. */
  def initial(t: EType): String = t match
    case EType.Int                 => "0"
    case EType.Bool                => "false"
    case EType.Unit                => "tt"
    case EType.Ref                 => "null"
    case EType.Several(Nil)        => "tt"
    case EType.Several(one :: Nil) => initial(one)
    case EType.Several(of)         => of.map(initial).mkString("(", ", ", ")")
