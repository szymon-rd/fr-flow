package frflow.proof.rocq.threads

import frflow.core.threads.{Ctor, Decl, Param}
import frflow.proof.rocq.threads.PrintTerm.{Bars, Place}

/** Rocq's text of a declaration of a thread program's file: a record, an inductive type (with one constructor,
  * on one line and without a bar), a definition.
  */
private[threads] object PrintDecl:
  private val Width = 110

  def params(ps: List[Param]): String = ps.map(p => s" (${p.name} : ${PrintTerm.ty(p.ty)})").mkString

  def ctor(c: Ctor): String = c.name + params(c.params)

  def apply(d: Decl)(using Bars): String = d match
    case Decl.Record(name, fields)                   =>
      s"Record $name := ${Decl.maker(name)} {\n" + fields.map(f =>
        s"  ${Decl.projection(name, f.name)} : ${PrintTerm.ty(f.ty)}").mkString(";\n") + " }."
    case Decl.Inductive(name, List(only))            => s"Inductive $name := ${ctor(only)}."
    case Decl.Inductive(name, ctors)                 =>
      s"Inductive $name :=\n" + ctors.map(c => s"  | ${ctor(c)}").mkString("\n") + "."
    case Decl.Definition(name, ps, result, body)     =>
      val head = s"Definition $name${params(ps)} : ${PrintTerm.ty(result)} :="
      val one = PrintTerm.flat(body, Place.Top)
      if head.length + one.length + 2 <= Width && !one.contains(";;") then s"$head $one."
      else s"$head\n  ${PrintTerm.lines(body, Place.Top, 2)}."
