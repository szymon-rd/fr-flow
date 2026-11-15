package frflow.executions.sets

import frflow.core.ty.DataType
import frflow.project.Projects
import frflow.proof.layout.ExecutionsLibrary
import java.nio.file.{Files, Paths}

/** The vocabulary's types have one Rocq text, in FrFlow's library: it is what FrFlow generates from the Scala that
  * declares them, and a model that names them imports it.
  */
class LibrarySuite extends munit.FunSuite:
  private val declared: List[DataType] =
    Projects.elaborated(sets).theory.vocabulary.types.filter(ExecutionsLibrary.has)

  test("the library's module is what FrFlow generates from the vocabulary's types") {
    val generated = ExecutionsLibrary.source(declared)
    val kept = Paths.get("modules/proof/rocq/FrFlow/Executions.v")
    if !Files.exists(kept) || Files.readString(kept) != generated then
      val obtained = Paths.get("modules/executions/target/Executions.v")
      Files.createDirectories(obtained.getParent)
      Files.writeString(obtained, generated)
      fail(s"FrFlow/Executions.v is not what is generated: see $obtained")
  }

  test("the names of the fields the library declares are those of the vocabulary's records") {
    val fields = declared.collect { case DataType.Product(_, _, fs) => fs.map(_.name) }.flatten.toSet
    assertEquals(fields, ExecutionsLibrary.fields)
  }

  test("a model that names the vocabulary's types imports them, and declares none of them") {
    val types = Projects.bare(Projects.elaborated(sets)).rocq.files.collectFirst {
      case (f, text) if f.toString.endsWith("Sets/Types.v") => text }.getOrElse(fail("no Types"))
    assert(types.contains("From FrFlow Require Export Executions."), types)
    assert(!types.contains("Inductive Event"), types)
  }
