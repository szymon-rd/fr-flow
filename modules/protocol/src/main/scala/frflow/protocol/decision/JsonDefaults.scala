package frflow.protocol
package decision

import io.circe.derivation.Configuration

/** How the decisions' JSON reads a field it lacks: as the field's default. */
private[decision] object JsonDefaults:
  given Configuration = Configuration.default.withDefaults
