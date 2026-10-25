package frflow
package ledger
package signing

import frflow.protocol.*
import java.security.{PrivateKey, PublicKey}

/** The developer's key: the private key signs their decisions; the public one, filed in `.frflow/keys/NAME.pub`, verifies them. */
final case class DeveloperKey(signing: PrivateKey, public: PublicKey):
  def id: KeyId = Keys.id(public)
