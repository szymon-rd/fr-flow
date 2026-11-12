package frflow.project.rocq

import frflow.core.threads.{Assemble, Draft, Program}
import frflow.dsl.compiled.Inspect
import frflow.dsl.compiled.threads.ReadThreads
import frflow.proof.rocq.threads.{RocqAgreement, RocqThreads}
import java.nio.file.{Files, Path}

/** Ox's scopes and forks, read from the TASTy of its jar into Rocq (`docs/THREADS-GENERATOR.md`): what the
  * generator prints is `examples/ox/rocq/Ox/Gen.v`, which is `Code.v`, the same unit written by hand, comments and
  * spacing apart; and `Agree.v`, which Rocq checks. `FRFLOW_ROCQ_WRITE=1` writes the two files anew.
  */
class OxThreadsRocqSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  private val ox = Path.of("examples/ox/rocq/Ox")
  private lazy val draft: Draft = Inspect(classOf[_root_.ox.Ox])(q => ReadThreads(q, OxUnit.unit))
  private lazy val program: Program = Assemble(draft)
  private lazy val gen: String = RocqThreads.file(program, OxUnit.title)
  private lazy val agree: String = RocqAgreement.file(program, "Ox.Code", "Ox.Gen", OxUnit.reordered)
  private def code: String = Files.readString(ox.resolve("Code.v"))

  /** The sentences of a file that are not its types: its definitions, and the section of `interp`. */
  private def defined(sentences: List[String]): List[String] =
    sentences.filter(s => Set("Definition", "Section", "Variable", "End").exists(k => s.startsWith(k + " ")))

  test("the generator prints the Gen.v and Agree.v that are kept") {
    if sys.env.contains("FRFLOW_ROCQ_WRITE") then
      List("Gen.v" -> gen, "Agree.v" -> agree).foreach((file, text) => Files.writeString(ox.resolve(file), text))
    assertEquals(gen, Files.readString(ox.resolve("Gen.v")))
    assertEquals(agree, Files.readString(ox.resolve("Agree.v")))
  }

  test("Gen.v is Code.v, comments and spacing apart, but for the order of forkUnsupervised's parameters") {
    val (written, generated) = (RocqText.sentences(code), RocqText.sentences(gen))
    assertEquals(generated.map(RocqText.declared), written.map(RocqText.declared))
    val different = written.zip(generated).filter(_ != _)
    assertEquals(different.map((w, _) => RocqText.declared(w)), OxUnit.reordered.keys.toList.map("Definition " + _))
    // the one difference: `Code.v` takes the capability first, Ox's source (and so `Gen.v`) the closure
    different.foreach((w, g) => assertEquals(
      g.replace("( f : code ) ( x1 : OxError )", "( x1 : OxError ) ( f : code )"), w))
  }

  test("what is not read is chaos: `uninterruptible`, in runFinalizers, and nothing else") {
    assertEquals(draft.unread.map(_.what), List("ox.uninterruptible"))
    assertEquals(""" chaos "([^"]*)"""".r.findAllMatchIn(gen).map(_.group(1)).toList, List("ox.uninterruptible"))
  }

  test("Agree.v holds Gen.v's definitions word for word, and a lemma for each definition of Code.v") {
    val sentences = RocqText.sentences(agree)
    assertEquals(RocqText.between(sentences, "Module Over", "End Over"), defined(RocqText.sentences(gen)))
    val lemmas = "(?m)^Lemma (\\w+)_agrees : ".r.findAllMatchIn(agree).map(_.group(1)).toList
    val definitions = "(?m)^\\s*Definition (\\w+)".r.findAllMatchIn(RocqText.uncommented(code)).map(_.group(1)).toList
    assertEquals(lemmas, definitions)
  }

  test("Rocq reads Gen.v, and checks Agree.v: each definition is Code.v's by reflexivity".tag(Rocq)) {
    assertEquals(ThreadsRocq.failing(List("Ox/Code.v" -> code, "Ox/Gen.v" -> gen, "Ox/Agree.v" -> agree)), None)
  }
