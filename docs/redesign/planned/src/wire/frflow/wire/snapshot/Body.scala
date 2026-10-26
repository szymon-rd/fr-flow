package frflow.wire.snapshot

/** What a node of each kind has beyond the rows every node has. */
enum Body:
  /** Whether it is a leaf (`root_impl` takes it as a hypothesis), its expectations, the operations `idle` replaced. */
  case Claim(leaf: Boolean, expectations: List[String], idle: List[String])
  case Invariant(keptBy: List[String], exempt: List[String])
  case Contract(op: String, examples: List[ExampleRow], code: Option[CodeRow], tested: Option[TestRow],
      runCheck: Option[String])
  /** An assumption about an operation (its adapter's examples and code), a fact, or a model (its realizations). */
  case Assumption(op: Option[String], examples: List[ExampleRow], code: Option[CodeRow])
  case Definition(fixes: List[String])
  case Design(governs: List[String])
