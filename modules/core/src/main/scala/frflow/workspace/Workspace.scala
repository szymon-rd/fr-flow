package frflow.workspace

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.security.MessageDigest
import scala.jdk.CollectionConverters.*

/** Directory layout of a theory project.
  *
  * {{{
  * <root>/
  *   lean/                Lean workspace (lakefile.toml, FrFlowGen/, Proofs/, FrFlowAudit/)
  *   .frflow/ledger.json  approvals and check results
  *   .frflow/slices/      theory slices for agents
  *   THEORY.md            human-readable digest of the theory
  * }}}
  *
  * @param kernelPath path of the FrFlow Lean kernel package, relative to `leanDir`
  */
final case class Workspace(root: Path, kernelPath: String):
  def leanDir: Path = root.resolve("lean")
  def metaDir: Path = root.resolve(".frflow")
  def ledgerFile: Path = metaDir.resolve("ledger.json")
  def slicesDir: Path = metaDir.resolve("slices")
  def digestFile: Path = root.resolve("THEORY.md")
  def lean(rel: String): Path = leanDir.resolve(rel)

object Files2:
  def read(p: Path): Option[String] =
    if Files.isRegularFile(p) then Some(Files.readString(p, UTF_8)) else None

  /** Writes only when content differs. Returns true if the file changed. */
  def writeIfChanged(p: Path, content: String): Boolean =
    if read(p).contains(content) then false
    else
      Option(p.getParent).foreach(Files.createDirectories(_))
      Files.writeString(p, content, UTF_8)
      true

  def listFiles(dir: Path): Seq[Path] =
    if !Files.isDirectory(dir) then Nil
    else
      val s = Files.walk(dir)
      try s.iterator().asScala.filter(Files.isRegularFile(_)).toList
      finally s.close()

object Hashing:
  def sha256(text: String): String =
    MessageDigest.getInstance("SHA-256").digest(text.getBytes(UTF_8)).map("%02x".format(_)).mkString

  def short(hash: String): String = hash.take(12)
