package frflow
package check

import io.circe.Codec

/** A case that failed, kept so that every later run tries it first (`.frflow/counterexamples.json`, committed). */
final case class Counterexample(seed: Long, index: Int, size: Int, shown: String) derives Codec.AsObject
