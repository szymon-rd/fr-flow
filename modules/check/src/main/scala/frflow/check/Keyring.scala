package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.*
import java.nio.file.Paths
import java.security.PublicKey

/** The project's keys, as filed and as committed: what a decision counts by (`TrustedKeys`). */
object Keyring:
  /** The keys decisions count by, and the keys as filed now. */
  def read(ws: Workspace): IO[(TrustedKeys, List[(String, PublicKey)])] =
    for
      working <- KeyStore.filed(ws.keysDir)
      committed <- process.Git.at(ws.root).committed(ws.root.relativize(ws.keysDir).toString)
    yield (TrustedKeys.of(working, committed.map(_.flatMap((file, text) => decoded(file, text)))), working)

  private def decoded(file: String, text: String): Option[(String, PublicKey)] =
    Option.when(file.endsWith(".pub"))(Paths.get(file).getFileName.toString.stripSuffix(".pub")).flatMap(name =>
      text.linesIterator.map(_.trim).find(_.nonEmpty).flatMap(Keys.decodePublic(_).toOption).map(name -> _))
