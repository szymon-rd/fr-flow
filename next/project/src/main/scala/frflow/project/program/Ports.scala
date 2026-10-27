package frflow.project.program

import frflow.project.port.{Git, KeyRing, LedgerStore, ProjectFiles}

/** The algebras the programs read and write through: the project's files, the ledger's store, the repository, and
  * the keys.
  */
final case class Ports[F[_]](files: ProjectFiles[F], ledger: LedgerStore[F], git: Git[F], keys: KeyRing[F])
