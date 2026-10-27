package frflow.wire.snapshot

import io.circe.Codec

/** What testing a node's code found, as tools read it: the cases, the seed, what was tested, whether one failed. */
final case class TestRow(cases: Int, seed: Long, against: String, failed: Boolean) derives Codec.AsObject
