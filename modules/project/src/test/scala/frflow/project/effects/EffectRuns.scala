package frflow.project.effects

import frflow.core.effect.{ClassName, MethodName}
import frflow.proof.effect.Named

/** The Rocq file that says, of each scenario, what the run of its tree gives: the number the JVM gave. A
  * scenario is a method, with no input, of a class made with none; the trees call nothing outside the code read.
  * And that a call on no object, or on one of another class, does not run: on the first the JVM throws, and the
  * trees have no node for that yet; the second no typed code does.
  */
object EffectRuns:
  private val signature = "class field method outside field_ty method_in method_out outside_in outside_out exn"
  private val tables = "class_eq field_eq field_of method_of initial body nothing_outside"

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
       |Definition scenario (called : ref -> prog Z) : ran (exn + Z) :=
       |  gives $signature $tables (Nat.pow 10 6)
       |    (made <- new ${Named.cls(scenarios)} ;;
       |     call made ${method(scenarios, "new")} tt ;;;
       |     called made).
       |
       |${(gave.map(lemma(scenarios, _, _)) ++ stuck(scenarios, gave.head._1)).mkString("\n\n")}
       |""".stripMargin

  private def method(cls: ClassName, name: String): String = Named.method(MethodName(cls, name))

  private def lemma(scenarios: ClassName, name: String, gave: Int): String =
    val result = if gave < 0 then s"($gave)" else gave.toString
    s"""Lemma ${name}_gives :
       |  scenario (fun made => call made ${method(scenarios, name)} tt) = Gave (inr $result).
       |Proof. vm_compute. reflexivity. Qed.""".stripMargin

  private def stuck(scenarios: ClassName, first: String): List[String] = List(
    s"""Lemma on_no_object_is_stuck : scenario (fun _ => call null ${method(scenarios, first)} tt) = Stuck.
       |Proof. vm_compute. reflexivity. Qed.""".stripMargin,
    s"""Lemma on_another_class_is_stuck :
       |  scenario (fun made => call made ${method(ClassName("Counter"), "current")} tt ;;; ret 0) = Stuck.
       |Proof. vm_compute. reflexivity. Qed.""".stripMargin)
