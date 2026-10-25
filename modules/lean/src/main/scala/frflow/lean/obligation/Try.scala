package frflow
package lean
package obligation

import frflow.protocol.TryKind

/** A try, and `means`: what is wrong if Lean proves it. */
final case class Try(kind: TryKind, obligation: Obligation, means: String)
