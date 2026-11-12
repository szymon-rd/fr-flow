package frflow.project.port.rocq

import cats.effect.Async
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.project.process.{Command, Exited}
import frflow.proof.reading.{RocqOutput, RocqReport, RocqSource, Theorem}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** One module compiled by `rocq compile`, under the name Rocq loads it by. Rocq stops at a file's first error, so a
  * lemma whose proof it does not accept is given up (`Proof. Admitted.`, in a copy: the source is never changed) and
  * the file compiled again; the lemmas before it, accepted already, are given up too while the rest is tried, and
  * the file is compiled once more at the end with only the lemmas not accepted given up, which is what a module
  * importing it loads. Any other error leaves the file broken.
  */
final class RocqCompiler[F[_]: Async: Processes](dirs: RocqDirs, rocq: Command):
  /** What Rocq said of the module; none when it took longer than a compile may. */
  def apply(logical: String, source: Path, text: String): F[Option[RocqReport.File]] =
    prepared(logical) >> tried(Trying(logical, source, text, RocqSource.lemmas(text)), Map.empty, Set.empty)

  private final case class Trying(logical: String, source: Path, text: String, lemmas: List[Theorem]):
    val file: String = RocqDirs.file(logical)
    def givenUp(up: Set[String]): String = lemmas.filter(l => up(l.name)).foldLeft(text)((t, l) =>
      RocqSource.admitted(t, l).getOrElse(t))
    /** The lemma an error at `line` is in the proof of, when giving it up is yet to be tried. */
    def at(line: Int, open: Set[String]): Option[Theorem] =
      lemmas.find(l => l.from <= line && line <= l.to && !open(l.name) && RocqSource.admitted(text, l).isDefined)

  /** `open`: the lemmas not accepted, with what Rocq said; `passed`: those accepted, given up while the rest is
    * tried.
    */
  private def tried(t: Trying, open: Map[String, String], passed: Set[String]): F[Option[RocqReport.File]] =
    compiled(t, open.keySet ++ passed).flatMap {
      case Exited.TimedOut(_)                    => None.pure[F]
      case Exited.Code(0, _) if passed.nonEmpty  => tried(t, open, Set.empty)
      case Exited.Code(0, out)                   => Some(RocqReport.File(t.file, open, audits(t, out), None)).pure[F]
      case Exited.Code(_, error)                 =>
        RocqOutput.error(error).flatMap((line, said) => t.at(line, open.keySet).map(_ -> said)) match
          case Some((lemma, said)) =>
            tried(t, open + (lemma.name -> said), t.lemmas.takeWhile(_ != lemma).map(_.name).toSet -- open.keySet)
          case None                =>
            Some(RocqReport.File(t.file, Map.empty, Map.empty, Some(RocqOutput.plain(error)))).pure[F]
    }

  /** What each lemma the module audits rests on; none of them when Rocq printed anything else than one audit each
    * (fail closed: a lemma with no audit is not checked).
    */
  private def audits(t: Trying, out: String): Map[String, List[String]] =
    val (asked, printed) = (RocqSource.audited(t.text), RocqOutput.assumptions(out))
    if asked.size == printed.size then asked.zip(printed).toMap else Map.empty

  private def prepared(logical: String): F[Unit] = Async[F].blocking {
    Files.createDirectories(dirs.compiled(logical).getParent)
    Files.createDirectories(dirs.scratch(logical).getParent)
    RocqDirs.Roots.foreach(r => Files.createDirectories(dirs.out.resolve(r)))
  }

  /** One compile: of the source itself with nothing given up, else of a copy. */
  private def compiled(t: Trying, up: Set[String]): F[Exited] =
    val from = if up.isEmpty then t.source.pure[F] else Async[F].blocking(
      Files.writeString(dirs.scratch(t.logical), t.givenUp(up), UTF_8))
    from.flatMap(file => Command.run(rocq, List("compile", "-q", "-noglob") ++ dirs.loadPath ++
      List("-top", t.logical, "-o", dirs.compiled(t.logical).toString, file.toString), dirs.out, Map.empty))
