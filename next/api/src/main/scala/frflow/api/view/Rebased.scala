package frflow.api.view

import frflow.core.name.RelPath

/** What `rebase` wrote: the ledger base's file, naming the SHA-256 of the ledger's text it accepts. It counts once it
  * is committed with the ledger.
  */
final case class Rebased(file: RelPath, ledger: String)
