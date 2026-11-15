package frflow.proof.rocq

import frflow.core.code.ReadUnit
import frflow.proof.layout.Lowering
import frflow.proof.prover.ast.*
import frflow.proof.rocq.threads.PrintData

/** The code a model's execution is of (`Code.Executing`), as Rocq: a module for each file read, holding its tree,
  * and `Code`: the files together, the table of what they define, and what it is for an execution to be one of
  * the code (`FrFlow.Code.Conforms`). Every statement that binds the execution takes that as a hypothesis
  * (`Lowering`).
  */
object CodeModules:
  def of(l: Lowering): List[ProverModule] = l.resolved.theory.code.read match
    case Nil => Nil
    case us  => us.map(unit(l, _)) :+ raw(l, l.layout.code, together(l, us))

  private def raw(l: Lowering, name: ModuleName, text: String): ProverModule =
    ProverModule(name, Nil, Preamble.generated, Names.path(l.kb.value), Nil, List(Decl.Rocq(text)))

  private def tree(u: ReadUnit): String = s"Code_${u.name}"

  private def unit(l: Lowering, u: ReadUnit): ProverModule =
    raw(l, l.layout.codeUnit(u.name), PrintData.file(tree(u), s"${u.name}, as the tree its TASTy holds.", u.tree))

  private def together(l: Lowering, us: List[ReadUnit]): String =
    val logical = (u: ReadUnit) => RocqProject.logical(l.layout.codeUnit(u.name))
    s"""From FrFlow Require Import Executions.
       |From Stdlib Require Import List.
       |Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Code.Conforms.
       |${us.map(u => s"Require Import ${logical(u)}.").mkString("\n")}
       |Import ListNotations.
       |
       |(** The files of the code read. *)
       |Definition Code_files : list tree := [${us.map(tree).mkString("; ")}].
       |
       |(** What they define. *)
       |Definition Code_table : table := Eval vm_compute in build Code_files.
       |
       |(** The execution is one of the code. *)
       |Definition Code_runs (history : Z -> Event) : Prop := runs Code_files Code_table history.""".stripMargin
