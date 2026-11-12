package frflow.proof.lean

import frflow.proof.layout.MiniProject
import frflow.proof.rocq.RocqProject

/** The Rocq printed from a theory's generated modules: text only, no Rocq run (`sbt rocqTest` runs `coqc`). */
class RocqProjectSuite extends munit.FunSuite:
  private val project = RocqProject(MiniProject.modules)
  private def text(file: String): String =
    project.files.toMap.getOrElse(file, fail(s"$file is not printed: ${project.files.map(_._1)}"))

  test("a record is printed with its fields named by it, and what reads and replaces each") {
    val types = text(s"FrFlowGen/${MiniProject.kb}/Types.v")
    assert(types.startsWith(RocqProject.header + "From FrFlow Require Export Base.\n"), types.take(200))
    assert(types.contains("Record Booking := Booking_mk {"), types)
    assert(types.contains("Class Has_start (R : Type) := { start_is : Type; start_of : R -> start_is }."), types)
    assert(types.contains("#[global] Instance Booking_has_start : Has_start Booking := {| start_of := " +
      "Booking_start |}."), types)
  }

  test("a module is printed after those it imports, each import exported") {
    val order = project.files.map(_._1)
    project.files.foreach { (file, written) =>
      "(?m)^Require Export ([A-Za-z0-9_.]+)\\.$".r.findAllMatchIn(written).map(_.group(1).replace('.', '/') + ".v")
        .foreach(i => assert(order.indexOf(i) >= 0 && order.indexOf(i) < order.indexOf(file), s"$file after $i"))
    }
  }

  test("a module with a form Rocq is not printed from yet is left out, named with the form") {
    assert(project.unprinted.keySet.intersect(project.files.map(_._1.stripSuffix(".v").replace('/', '.')).toSet)
      .isEmpty)
    assert(project.unprinted.values.forall(_.nonEmpty))
  }
