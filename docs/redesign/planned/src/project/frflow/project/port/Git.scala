package frflow.project.port

/** The repository: the commit a decision is stamped with, and the diff of governed files since a decision's commit.
  * An algebra for its in-memory interpreter in the decision and review tests (no repository needed).
  */
trait Git[F[_]]:
  def head: F[Option[String]]
  def diff(since: String, files: List[String]): F[String]
