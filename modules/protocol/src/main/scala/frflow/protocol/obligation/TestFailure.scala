package frflow.protocol
package obligation

import io.circe.Codec

final case class TestFailure(shown: String, why: String, seed: Long, index: Int, size: Int) derives Codec.AsObject
