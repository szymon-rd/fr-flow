package frflow.protocol
package snapshot

import io.circe.Codec

/** How a contract's code is checked where it runs, against what, and whether the developer chose it. */
final case class RunTime(check: RunCheck, against: String, chosen: Boolean) derives Codec.AsObject:
  def describe: String = check match
    case RunCheck.Never => s"at run time: not checked, the running code is the code Lean proves${if chosen then " (chosen)" else ""}"
    case c              => s"at run time: $against, checked on ${c.describe}${if chosen then " (chosen)" else " (the default for code not proven)"}"
