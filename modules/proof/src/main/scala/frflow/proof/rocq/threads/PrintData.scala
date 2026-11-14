package frflow.proof.rocq.threads

import frflow.core.threads.Datum

/** Data as a Rocq term (`core.threads.Datum`): a constructor applied in parentheses, a list in brackets, a text in
  * quotes. A term that does not fit a line is broken after the parts that do, each of the others on lines of its
  * own, two columns in.
  */
object PrintData:
  private val Width = 118

  def apply(d: Datum, indent: Int): String = lines(d, indent).map(l => " " * indent + l).mkString("\n")

  /** The file that defines `name` as `d`, a tree of `FrFlow.Scala.Tree`; `title` says what was read. */
  def file(name: String, title: String, d: Datum): String =
    s"""(** $title *)
       |
       |From Stdlib Require Import String List ZArith.
       |Require Import FrFlow.Scala.Tree.
       |Import ListNotations.
       |Open Scope string_scope.
       |
       |Definition $name : tree :=
       |${apply(d, 2)}.
       |""".stripMargin

  /** What encloses a term's parts, and what separates them. */
  private enum Around(val open: String, val separator: String, val close: String):
    case Applied(constructor: String) extends Around(s"($constructor ", " ", ")")
    case Listed extends Around("[", "; ", "]")

  private def lines(d: Datum, indent: Int): List[String] = d match
    case Datum.Of(c, Nil)     => List(c)
    case Datum.Of(c, args)    => enclosed(Around.Applied(c), args.map(lines(_, indent + 2)), indent)
    case Datum.Text(s)        => List("\"" + s.replace("\"", "\"\"") + "\"")
    case Datum.Nat(n)         => List(n.toString)
    case Datum.Whole(z)       => List(s"($z)%Z")
    case Datum.Truth(b)       => List(b.toString)
    case Datum.Many(Nil)      => List("[]")
    case Datum.Many(elems)    => enclosed(Around.Listed, elems.map(lines(_, indent + 2)), indent)
    case Datum.Maybe(None)    => List("None")
    case Datum.Maybe(Some(x)) => enclosed(Around.Applied("Some"), List(lines(x, indent + 2)), indent)

  /** The parts enclosed: on one line where they fit; else each part on its own lines, two columns in. */
  private def enclosed(around: Around, parts: List[List[String]], indent: Int): List[String] =
    val one = around.open + parts.map(_.head).mkString(around.separator) + around.close
    if parts.forall(_.sizeIs == 1) && one.length + indent <= Width then List(one)
    else
      val separated = parts.zipWithIndex.map((p, i) =>
        if around == Around.Listed && i < parts.size - 1 then p.init :+ (p.last + ";") else p)
      val body = separated.flatten.map("  " + _)
      (around.open.trim :: body.init) :+ (body.last + around.close)
