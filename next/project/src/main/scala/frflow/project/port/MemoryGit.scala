package frflow.project.port

import cats.Monad
import cats.effect.Ref
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.decision.content.Sha

/** Commits in memory, each the whole tree as committed: the decision tests run without a repository. `commit`
  * records the files given over the last commit's, under a hash of the commit's order and files.
  */
final class MemoryGit[F[_]: Monad] private (commits: Ref[F, Vector[(String, Map[RelPath, String])]]) extends Git[F]:
  def head: F[Option[String]] = commits.get.map(_.lastOption.map(_._1))
  def committed(p: RelPath): F[Option[String]] = commits.get.map(_.lastOption.flatMap(_._2.get(p)))

  /** Each version the commits hold, oldest first, a commit that left it as it was not counted again. */
  def versions(p: RelPath): F[List[String]] = commits.get.map(cs =>
    cs.toList.flatMap(_._2.get(p)).foldLeft(List.empty[String])((vs, v) => if vs.lastOption.contains(v) then vs
      else vs :+ v))

  def diff(since: String, files: List[RelPath]): F[String] = "".pure[F]

  def commit(files: Map[RelPath, String]): F[String] = commits.modify { cs =>
    val tree = cs.lastOption.fold(Map.empty[RelPath, String])(_._2) ++ files
    val sha = Sha.parts(cs.size.toString :: tree.toList.sortBy(_._1).flatMap((p, t) => List(p.value, t))*)
    (cs :+ (sha -> tree), sha)
  }

object MemoryGit:
  def apply[F[_]: Monad: Ref.Make]: F[MemoryGit[F]] =
    Ref.of[F, Vector[(String, Map[RelPath, String])]](Vector.empty).map(new MemoryGit(_))
