package links

import frflow.*

// The link shortener's model: the claims on its three members, and the class that implements them, proven to meet
// each. What removing does is stated exactly, and follows from its two cases, each proven of the code.

val links: FrModel = FrModel("Shortener")(
  Links.shortenIsIdempotent,
  Links.shortenedCodeResolves,
  Links.shortenKeepsExistingLinks,
  Links.removeChangesOnlyThatCode,
  Links.removedCodeLeadsNowhere.refines(Links.removeChangesOnlyThatCode),
  Links.removeKeepsOtherCodes.refines(Links.removeChangesOnlyThatCode),
  Links.removedCodeNotReissued,
  Links.shortener.define(lifted[RetiringLinks]))
