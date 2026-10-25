package frflow.protocol

/** A decision below a changed node: `moved` is under review only because the node's meaning moved. */
enum BelowKind:
  case Accepted, Moved
  override def toString: String = word(productPrefix)

object BelowKind extends Words[BelowKind]
