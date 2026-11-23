package frflow.project.effects

import frflow.core.effect.{ClassName, MethodName}
import frflow.proof.effect.Named

/** The Rocq file that says, of each scenario, what the run of its tree gives: the number the JVM gave. A
  * scenario is a method, with no input, of a class made with none; the trees call nothing outside the code read.
  */
object EffectRuns:
  private val signature = "class field method outside field_ty method_in method_out outside_in outside_out exn"

  def file(program: String, scenarios: ClassName, gave: List[(String, Int)]): String =
    s"""From Stdlib Require Import ZArith List.
       |From FrFlow.Effect Require Import Tree Int32 Sig Run.
       |Require Import $program.
       |Open Scope Z_scope.
       |Open Scope effect_scope.
       |
       |Definition nothing_outside (m : outside) :
       |  outside_in m -> heap class field field_ty -> option ((exn + outside_out m) * heap class field field_ty) :=
       |  match m with end.
       |
       |(** What a method of the scenarios gives, called on an object of theirs just made, from an empty heap. *)
       |Definition scenario (called : ref -> prog Z) : option (exn + Z) :=
       |  gives $signature field_eq initial body nothing_outside (Nat.pow 10 6)
       |    (made <- new ${Named.cls(scenarios)} ;;
       |     call ${Named.method(MethodName(scenarios, "new"))} made ;;;
       |     called made).
       |
       |${gave.map(lemma(scenarios, _, _)).mkString("\n\n")}
       |""".stripMargin

  private def lemma(scenarios: ClassName, name: String, gave: Int): String =
    val result = if gave < 0 then s"($gave)" else gave.toString
    s"""Lemma ${name}_gives :
       |  scenario (fun made => call ${Named.method(MethodName(scenarios, name))} made) = Some (inr $result).
       |Proof. vm_compute. reflexivity. Qed.""".stripMargin
