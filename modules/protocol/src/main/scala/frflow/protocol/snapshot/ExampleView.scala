package frflow.protocol
package snapshot

import io.circe.Codec

/** An example of a claim: what fails of it in Scala, and what Lean computes of it; `asWritten`, one written as a
  * test, as written.
  */
final case class ExampleView(note: String, `given`: List[String], call: String, expected: Boolean, fails: Option[String],
    codeFails: Option[String], lean: Option[Outcome], leanImplementation: Option[Outcome],
    asWritten: Option[String] = None)
    derives Codec.AsObject:
  def passes: Boolean = fails.isEmpty && codeFails.isEmpty
