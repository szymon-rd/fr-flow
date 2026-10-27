package frflow.proof.verdict

/** What a node's check depends on; the node is checked again when it moves. */
opaque type CheckKey = String

object CheckKey:
  def apply(sha: String): CheckKey = sha
  extension (k: CheckKey) def value: String = k
