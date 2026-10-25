package frflow
package check

import frflow.protocol.*
import io.circe.Codec

/** A test result, with the hash of what it depends on: kept while that holds (`.frflow/tests.json`, derived, not committed). */
final case class Recorded(key: Hash, report: TestReport) derives Codec.AsObject
