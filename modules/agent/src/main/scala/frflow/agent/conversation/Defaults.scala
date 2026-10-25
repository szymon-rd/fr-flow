package frflow.agent
package conversation

import io.circe.derivation.Configuration

/** How the conversation's records are read from JSON: a field left out takes its default. */
private[agent] object Defaults:
  given Configuration = Configuration.default.withDefaults
