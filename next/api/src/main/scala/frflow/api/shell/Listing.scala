package frflow.api.shell

import cats.effect.Sync
import cats.syntax.all.*
import frflow.api.view.{Listed, Stop}
import frflow.decision.ledger.{Decider, Deciders}
import frflow.project.port.{KeyRing, Keys}
import frflow.project.program.Config
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.DecidersFile
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** The first deciders' list of a project: the developer's key (`FRFLOW_KEY`, else the default under `HOME`) listed
  * under `name`, sealed by that key, written to `.frflow/deciders` unless a list is there already. The key is read,
  * never made.
  */
private[api] object Listing:
  def first[F[_]: Sync](root: Path, name: String, env: Map[String, String]): F[Listed] =
    val file = root.resolve(KeyRing.path.value)
    Sync[F].blocking(Files.exists(file)).ifM(Listed.Already(KeyRing.path).pure[F],
      key(env).flatMap((priv, pub) => Sync[F].blocking {
        val id = Keys.id(pub)
        val list = Deciders(List(Decider(name, id, pub)), None, None)
        val _ = Files.createDirectories(file.getParent)
        val _ = Files.writeString(file, Wire.print(DecidersFile.format,
          list.copy(seal = Some(Keys.signer(priv, id)(list.payload)))), UTF_8)
        Listed.Written(KeyRing.path)
      }))

  private def key[F[_]: Sync](env: Map[String, String]): F[(java.security.PrivateKey, String)] =
    Config.keyFile(env).fold(Sync[F].raiseError(Stop.NoKey("FRFLOW_KEY (or HOME) not set")))(f =>
      Sync[F].blocking(Option.when(Files.isRegularFile(f))(Files.readString(f, UTF_8)))
        .flatMap(_.toRight(Stop.NoKey(f.toString)).liftTo[F])
        .flatMap(t => Keys.read(t).leftMap(Stop.NotAKey(f.toString, _)).liftTo[F]))
