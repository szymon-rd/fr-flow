package frflow.wire

import frflow.core.name.NodeId
import frflow.wire.check.ChecksFile
import frflow.wire.file.{Depth, FileFormat, Files, Unreadable}
import frflow.wire.ledger.{DecidersFile, LedgerFile}
import frflow.wire.sample.LedgerSamples
import frflow.wire.snapshot.Snapshot
import frflow.wire.test.TestsFile
import io.circe.Json

/** A file that does not read says which file, which field and which version. */
class UnreadableSuite extends munit.FunSuite:
  private val formats: List[FileFormat[?]] = List(LedgerFile.format, DecidersFile.format, ChecksFile.format,
    TestsFile.format, TestsFile.counterexamples, Snapshot.format)

  /** The ref of the golden ledger's one design content. */
  private val design = LedgerSamples.ledger.history(NodeId("Free")).head.bound.content.ref

  /** A golden file with its first `from` replaced by `to`. */
  private def golden(name: String, from: String, to: String): String =
    val text = scala.io.Source.fromResource(s"golden/$name")(using scala.io.Codec.UTF8).mkString
    assert(text.contains(from), from)
    text.replaceFirst(java.util.regex.Pattern.quote(from), java.util.regex.Matcher.quoteReplacement(to))

  test("each file names itself when it is not JSON, has no version, or has another version") {
    formats.foreach { f =>
      assertEquals(Files.read(f, "{\"version\": 1,").left.map(_.file), Left(f.file))
      assertEquals(Files.read(f, "{}"), Left(Unreadable.NoVersion(f.file)))
      assertEquals(Files.read(f, "{\"version\": \"1\"}"), Left(Unreadable.NoVersion(f.file)))
      assertEquals(Files.read(f, "{\"version\": 2}"), Left(Unreadable.UnknownVersion(f.file, 2, 1)))
    }
  }

  test("a field that does not read is named by its path, with the version read") {
    assertEquals(Files.read(LedgerFile.format, golden("ledger.json", "\"revisit\"", "\"approve\"")),
      Left(Unreadable.BadField(".frflow/ledger.json", 1, ".decisions.Root[1].action", "no action approve")))
    assertEquals(Files.read(ChecksFile.format, golden("checks.json", "\"status\": \"failed\",", "")),
      Left(Unreadable.BadField(".frflow/checks.json", 1, ".checks.Book.status", "missing")))
    assertEquals(Files.read(TestsFile.format, golden("tests.json", "\"kind\": \"claim\"", "\"kind\": \"rule\"")),
      Left(Unreadable.BadField(".frflow/tests.json", 1, ".tests.Book.against.kind", "no test target of kind rule")))
    assertEquals(Files.read(Snapshot.format, golden("kb.json", "\"cases\": 500", "\"cases\": \"many\"")),
      Left(Unreadable.BadField(".frflow/kb.json", 1, ".nodes[0].body.tested.cases", "not a whole number")))
  }

  test("a decision naming a content the ledger does not hold does not read") {
    assertEquals(Files.read(LedgerFile.format, golden("ledger.json", s"\"$design\": {", "\"other\": {")),
      Left(Unreadable.BadField(".frflow/ledger.json", 1, ".decisions.Free[0].content",
        s"no content $design in the ledger's contents")))
  }

  test("a content's field is a text, texts or a record of texts") {
    assertEquals(Files.read(LedgerFile.format, golden("ledger.json", "\"kind\": \"design\"", "\"kind\": 3")),
      Left(Unreadable.BadField(".frflow/ledger.json", 1, s".contents.$design.kind",
        "a field is a text, a list of texts or a record of texts")))
  }

  test("an obligation's name that is not one is named") {
    assertEquals(Files.read(ChecksFile.format, golden("checks.json", "\"name\": \"impl\"", "\"name\": \"proof\"")),
      Left(Unreadable.BadField(".frflow/checks.json", 1, ".checks.Book.results[0].name", "no obligation proof")))
  }

  /** `depth` arrays, one inside the other, around an empty one. */
  private def nested(depth: Int): Json = (1 to depth).foldLeft(Json.arr())((j, _) => Json.arr(j))

  test("a file nested deeper than the codecs may recurse is refused, naming where, without overflowing the stack") {
    val deep = Json.obj("version" -> Json.fromInt(1), "counterexamples" -> Json.obj("Book" -> nested(5000)))
    val path = ".counterexamples.Book" + "[0]" * (Depth.limit - 1)
    assertEquals(Files.decode(TestsFile.counterexamples, deep),
      Left(Unreadable.BadField(".frflow/counterexamples.json", 1, path, s"nested deeper than ${Depth.limit}")))
    val text = golden("counterexamples.json", "\"kind\": \"str\",", s"\"deep\": ${nested(2000).noSpaces},")
    assertEquals(Files.read(TestsFile.counterexamples, text).left.map {
      case Unreadable.BadField(file, _, _, problem) => s"$file: $problem"
      case other                                    => other.toString
    }, Left(s".frflow/counterexamples.json: nested deeper than ${Depth.limit}"))
  }

  test("a document as deep as the limit is not beyond it; one level more is") {
    assertEquals(Depth.beyond(nested(Depth.limit)), None)
    assertEquals(Depth.beyond(nested(Depth.limit + 1)), Some("[0]" * (Depth.limit + 1)))
  }
