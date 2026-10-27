package frflow.decision.ledger

/** Why a decision in the ledger does not count: no deciders' list is committed (or its versions do not follow one
  * another); it has no seal, or its seal's key is not listed under its decider's name; its signature does not verify;
  * the node's history in a committed version is not where its history in the next one, or now, starts (a decision
  * was taken out or changed; a decision only committed is reported so too); or a committed version of the ledger
  * does not read, so nothing counts.
  */
enum Uncounted:
  case NoDeciders, NotListed, NotVerified, Rewritten, Unreadable
