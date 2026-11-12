package frflow.project.rocq

import frflow.core.name.NodeId
import frflow.proof.reading.ProofFile
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The developer's Rocq proof files of an example (`rocq/Proofs/<Model>/<node>.v`): a lemma named
  * `<node>_Proofs_<obligation>` proves that obligation of the node (`neverCommitsAhead_Proofs_impl`).
  */
object RocqProofs:
  /** Each proof file under `rocq`, by its path from there (`Proofs/Payments/Lemmas.v`). */
  def of(rocq: Path): Map[String, String] =
    if !Files.isDirectory(rocq.resolve("Proofs")) then Map.empty
    else
      val all = Files.walk(rocq.resolve("Proofs"))
      try all.iterator.asScala.filter(_.toString.endsWith(".v")).map(p =>
        rocq.relativize(p).toString -> Files.readString(p)).toMap
      finally all.close()

  /** What the files prove, as the analysis reads it of a proof file: for each node's file, a theorem for each
    * obligation a lemma of it is named for. The analysis reads Lean's proof files today, so each is given as the
    * head of a Lean theorem; only its name is read.
    */
  def stated(proofs: Map[String, String]): Map[NodeId, ProofFile] = proofs.flatMap { (file, text) =>
    val node = file.split('/').last.stripSuffix(".v")
    val lemmas = s"(?m)^Lemma ${node}_Proofs_([A-Za-z0-9_]+)".r.findAllMatchIn(text).map(_.group(1)).toList
    Option.when(lemmas.nonEmpty)(NodeId(node) -> ProofFile(NodeId(node),
      lemmas.map(l => s"theorem $l : Obl.$l := by\n  sorry\n").mkString("\n")))
  }
