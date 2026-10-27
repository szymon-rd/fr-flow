package frflow.wire

import frflow.wire.check.ChecksFile
import frflow.wire.file.{FileFormat, Files}
import frflow.wire.ledger.{DecidersFile, LedgerFile}
import frflow.wire.snapshot.Snapshot
import frflow.wire.test.TestsFile
import org.scalacheck.{Gen, Prop}

/** Every file reads back what was written: a drawn value, printed and read, is the value again; and printing it again
  * gives the same text.
  */
class RoundTripSuite extends munit.ScalaCheckSuite:
  override def scalaCheckTestParameters = super.scalaCheckTestParameters.withMinSuccessfulTests(300)

  private def roundTrip[A](f: FileFormat[A], draw: Gen[A]): Prop = Prop.forAll(draw) { a =>
    val text = Files.print(f, a)
    assertEquals(Files.read(f, text), Right(a), text)
    assertEquals(Files.read(f, text).map(Files.print(f, _)), Right(text))
  }

  property("the ledger")(roundTrip(LedgerFile.format, LedgerDraws.ledger))
  property("the deciders' list")(roundTrip(DecidersFile.format, LedgerDraws.deciders))
  property("the checks")(roundTrip(ChecksFile.format, CheckDraws.checks))
  property("the tests")(roundTrip(TestsFile.format, TestDraws.tests))
  property("the counterexamples")(roundTrip(TestsFile.counterexamples, TestDraws.counterexamples))
  property("the snapshot")(roundTrip(Snapshot.format, SnapshotDraws.snapshot))
