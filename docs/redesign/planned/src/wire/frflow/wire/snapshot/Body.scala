package frflow.wire.snapshot

/** What a node has beyond the rows every node has: a statement (claimed or assumed), or a design. */
enum Body:
  /** How it is checked (`Checking`, in words), the Definition it reads as a call of, the code of the Definitions it
    * mentions and their tests.
    */
  case Stated(checking: List[String], call: Option[String], code: Option[CodeRow], tested: Option[TestRow])
  case Design(governs: List[String])
