package frflow.wire.snapshot

import io.circe.Codec

/** What testing a node's code found, as tools read it: the cases, the seed (a whole number written as a string, so a
  * reader that rounds numbers keeps it), what was tested, whether one failed.
  */
final case class TestRow(cases: Int, seed: String, against: String, failed: Boolean) derives Codec.AsObject
