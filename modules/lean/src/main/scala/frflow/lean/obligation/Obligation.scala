package frflow
package lean
package obligation

import frflow.protocol.ObligationName

final case class Obligation(name: ObligationName, statement: String, description: String)
