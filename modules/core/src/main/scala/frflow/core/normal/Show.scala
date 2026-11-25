package frflow.core.normal

import frflow.core.effect.EType

/** Normalised Scala as text, for people: one statement a line, a block two columns in. */
object Show:
  def apply(p: NormalProgram): String = p.methods.map(method).mkString("\n\n") + "\n"

  private def method(m: NormalMethod): String =
    val params = m.params.map((l, t) => s"${local(l)}: ${ty(t)}").mkString(", ")
    (s"method ${m.name.cls.value}.${m.name.name}($params): ${ty(m.gives)}" :: in(block(m.body))).mkString("\n")

  private def ty(t: EType): String = t match
    case EType.Int         => "Int"
    case EType.Bool        => "Boolean"
    case EType.Unit        => "Unit"
    case EType.Ref         => "Ref"
    case EType.Several(of) => of.map(ty).mkString("(", ", ", ")")

  private def local(l: Local): String = s"${l.name}#${l.id}"

  private def atom(a: Atom): String = a match
    case Atom.Of(l)    => local(l)
    case Atom.Whole(n) => n.toString
    case Atom.Truth(b) => b.toString
    case Atom.Nothing  => "()"
    case Atom.NoObject => "null"
    case Atom.Self     => "this"

  private def in(lines: List[String]): List[String] = lines.map("  " + _)

  private def block(b: Block): List[String] = b.stmts.flatMap(stmt) :+ atom(b.gives)

  private def stmt(s: Stmt): List[String] = s match
    case Stmt.Val(l, t, r, temp)   => bound(s"${if temp then "tmp" else "val"} ${local(l)}: ${ty(t)} = ", r)
    case Stmt.Var(l, t, a)         => List(s"var ${local(l)}: ${ty(t)} = ${atom(a)}")
    case Stmt.Assign(l, a)         => List(s"${local(l)} = ${atom(a)}")
    case Stmt.Write(on, f, v)      => List(s"${atom(on)}.${f.name} = ${atom(v)}")
    case Stmt.Loop(test, body)     => ("while {" :: in(block(test))) ++ ("} do {" :: in(block(body))) :+ "}"
    case Stmt.Run(r)               => bound("", r)

  private def bound(head: String, r: Rhs): List[String] = r match
    case Rhs.Choice(t, yes, no) =>
      (s"${head}if ${atom(t)} then {" :: in(block(yes))) ++ ("} else {" :: in(block(no))) :+ "}"
    case other                  => List(head + simple(other))

  private def simple(r: Rhs): String = r match
    case Rhs.Is(a)                             => atom(a)
    case Rhs.Applied(op, args)                 => args.map(atom).mkString(s"$op(", ", ", ")")
    case Rhs.Read(on, f)                       => s"${atom(on)}.${f.name}"
    case Rhs.Make(c)                           => s"new ${c.value}"
    case Rhs.Call(Kind.Static(m), on, args)    =>
      (on :: args).map(atom).mkString(s"call(static ${m.cls.value}.${m.name}, ", ", ", ")")
    case Rhs.Call(Kind.External(o), on, args)  =>
      (on :: args).map(atom).mkString(s"call(external ${o.owner}.${o.name}, ", ", ", ")")
    case Rhs.Choice(_, _, _)                   => "if"
