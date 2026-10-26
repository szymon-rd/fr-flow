package frflow
package check

import java.nio.file.Path

/** Where a project lives: `lean/` (`FrFlowGen/` generated, `Proofs/` authored) and `.frflow/` (the ledger and keys
  * committed; checks and snapshot derived; a layer on top keeps its own files there too). `kernelPath`: FrFlow's Lean
  * kernel, relative to `lean/`.
  */
final case class Workspace(root: Path, kernelPath: String):
  def lean: Path = root.resolve("lean")
  def ledgerFile: Path = root.resolve(".frflow/ledger.json")
  def checksFile: Path = root.resolve(".frflow/checks.json")
  def testsFile: Path = root.resolve(".frflow/tests.json")
  def counterexamplesFile: Path = root.resolve(".frflow/counterexamples.json")
  def snapshotFile: Path = root.resolve(".frflow/kb.json")
  def consistencyFile: Path = root.resolve(".frflow/consistency.json")
  def keysDir: Path = root.resolve(".frflow/keys")
