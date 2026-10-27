package frflow.project.port

import cats.Functor
import cats.effect.Sync
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.decision.ledger.{Deciders, Seals}
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.DecidersFile
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** The developer's signing key, and who may decide: the committed deciders' list (`Deciders.committed` over the
  * file's committed versions, read through `Git`) and a verifier of its keys. Interpreters: the key's file and git
  * (`make`), and a key made in memory (`MemoryKeys`), so tests never touch the developer's key. Laws: a seal `signer`
  * makes names `key`; `verifier` is total (false on what is not a signature by a listed key); `deciders` is none when
  * a committed version does not read or does not follow the one before.
  */
trait KeyRing[F[_]]:
  def signer: F[Seals.Signer]
  /** The id of the key `signer` signs with. */
  def key: F[String]
  def verifier: F[Seals.Verifier]
  def deciders: F[Option[Deciders]]

object KeyRing:
  /** The key at `keyFile` (`FRFLOW_KEY`, or `~/.config/frflow/signing.key`), read only: none there is raised
    * (`FrFlowError.NoKey`), never made here.
    */
  def make[F[_]: Sync](keyFile: Path, git: Git[F]): KeyRing[F] = Listed(git,
    Sync[F].blocking(Option.when(Files.isRegularFile(keyFile))(Files.readString(keyFile, UTF_8)))
      .flatMap(_.toRight(FrFlowError.NoKey(keyFile.toString)).liftTo[F])
      .flatMap(t => Keys.read(t).leftMap(FrFlowError.NotAKey(keyFile.toString, _)).liftTo[F]))

  /** No key at hand (the environment names none): signing raises `NoKey`; who may decide is still read from git. */
  def keyless[F[_]: Sync](git: Git[F]): KeyRing[F] =
    Listed(git, Sync[F].raiseError(FrFlowError.NoKey("FRFLOW_KEY (or HOME) not set")))

  /** The key `read` gives, and the committed deciders' list. */
  private final class Listed[F[_]: Sync](git: Git[F], read: F[(java.security.PrivateKey, String)])
      extends KeyRing[F]:
    def signer: F[Seals.Signer] = read.map((k, pub) => Keys.signer(k, Keys.id(pub)))
    def key: F[String] = read.map((_, pub) => Keys.id(pub))
    def verifier: F[Seals.Verifier] = versions(git).map(vs => Keys.verifier(vs.toList.flatten.flatMap(_.entries)))
    def deciders: F[Option[Deciders]] = versions(git).map(_.flatMap(KeyRing.committed))

  /** The committed versions of the deciders' list, oldest first; none when one does not read. */
  def versions[F[_]: Functor](git: Git[F]): F[Option[List[Deciders]]] =
    git.versions(path).map(_.traverse(Wire.read(DecidersFile.format, _).toOption))

  /** The list that counts, of versions each following the one before. */
  def committed(versions: List[Deciders]): Option[Deciders] =
    Deciders.committed(versions, Keys.verifier(versions.flatMap(_.entries)))

  /** `.frflow/deciders`. */
  val path: RelPath = RelPath.fromIdentifiers(".frflow", "deciders")
