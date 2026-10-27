package frflow.wire

import frflow.wire.check.ChecksFile
import frflow.wire.file.{FileFormat, Files}
import frflow.wire.ledger.{DecidersFile, LedgerFile}
import frflow.wire.snapshot.Snapshot
import frflow.wire.test.TestsFile
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files as Disk, Path}
import scala.io.{Codec, Source}
import scala.util.Using

/** Each file's exact text, pinned: a sample printed is its golden file, and the golden file reads as the sample. A
  * change to a format changes its golden file, listed in the commit. A missing golden is written under `target/`
  * for review.
  */
class GoldenSuite extends munit.FunSuite:
  private def golden[A](name: String, f: FileFormat[A], sample: A)(using munit.Location): Unit =
    test(s"$name is written and read as pinned (${f.file})") {
      val printed = Files.print(f, sample)
      val pinned = Using(Source.fromResource(s"golden/$name", getClass.getClassLoader)(using Codec.UTF8))(_.mkString)
        .getOrElse(fail(s"no golden $name; written to ${obtained(name, printed)}"))
      assertNoDiff(printed, pinned)
      assertEquals(printed, pinned)
      assertEquals(Files.read(f, pinned), Right(sample))
    }

  private def obtained(name: String, text: String): Path =
    val p = Path.of("next/wire/target/golden-obtained", name)
    Disk.createDirectories(p.getParent)
    Disk.writeString(p, text, UTF_8)

  golden("ledger.json", LedgerFile.format, LedgerSamples.ledger)
  golden("deciders", DecidersFile.format, LedgerSamples.deciders)
  golden("checks.json", ChecksFile.format, CheckSamples.checks)
  golden("tests.json", TestsFile.format, TestSamples.tests)
  golden("counterexamples.json", TestsFile.counterexamples, TestSamples.counterexamples)
  golden("kb.json", Snapshot.format, SnapshotSamples.snapshot)
