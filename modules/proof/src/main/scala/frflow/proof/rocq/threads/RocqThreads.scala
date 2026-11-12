package frflow.proof.rocq.threads

import frflow.core.threads.{Ctor, Decl, Param, Program, Section, Ty}
import frflow.proof.rocq.threads.PrintTerm.Bars

/** A unit of code read as thread programs (`core.threads.Program`), as a Rocq file over
  * `modules/proof/rocq/FrFlow/Threads`: the types, the closures (`code`: one constructor for each closure the code
  * makes, and `Client` for the caller's), the globals and casts, the methods of the classes not read, the
  * definitions, and what each closure runs (`interp`).
  */
object RocqThreads:
  /** What a file over the library starts with. */
  val imports: String =
    """From Stdlib Require Import ZArith List Bool String.
      |Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Lang.
      |Import ListNotations.
      |Open Scope prog_scope.
      |Open Scope string_scope.
      |Set Warnings "-register-all".""".stripMargin

  /** The constructor of `code` for a closure of the caller's, with the capabilities it holds. */
  def client(p: Program): Ctor = Ctor("Client", List(Param("n", Ty.Nat), Param("caps", Ty.list(p.holds))))

  /** The file: `title` says what was read. */
  def file(p: Program, title: String): String =
    List(s"(** $title *)", imports, types(p), closures(p), definitions(p), interp(p, "")).mkString("\n\n") + "\n"

  private def heading(title: String): String = s"(** ** $title *)"

  def types(p: Program): String =
    (heading("The classes") :: p.types.map(PrintDecl(_)(using Bars.Leading))).mkString("\n\n")

  def closures(p: Program): String =
    List(heading("The closures"), PrintDecl(Decl.Inductive("code", p.closures :+ client(p)))(using Bars.Leading),
      "Abbreviation val := (Jdk.val code obj).\nAbbreviation M := (Lang.M code obj).").mkString("\n\n")

  /** Every definition after the types: the globals and casts, then each section. */
  def definitions(p: Program): String =
    val support = (heading("Globals and casts") :: p.support.map(PrintDecl(_)(using Bars.Inner))).mkString("\n\n")
    (support :: (p.externs ++ p.sections).map(section)).mkString("\n\n")

  private def section(s: Section): String =
    (heading(s.title) :: s.defs.map(PrintDecl(_)(using Bars.Leading))).mkString("\n\n")

  /** What each closure runs: the definition made for it; the caller's, what the caller says (`client`). */
  def interp(p: Program, indent: String): String =
    val arms = p.closures.map { c =>
      val captured = c.params.map(_.name).mkString(" ")
      s"    | ${c.name} $captured => ${c.name}_body $captured arg" }
    (List(heading("What each closure runs"), "", "Section Interp.", "", "  (** The caller's closures. *)",
      s"  Variable client : nat -> ${PrintTerm.ty(Ty.list(p.holds))} -> val -> M val.", "",
      "  Definition interp (c : code) (arg : val) : M val :=", "    match c with") ++ arms ++
      List("    | Client n caps => client n caps arg", "    end.", "", "End Interp.")).map(l =>
      if l.isEmpty then l else indent + l).mkString("\n")
