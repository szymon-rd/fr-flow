package frflow.decision.ledger

/** Why a decision in the ledger does not count: no deciders' list is committed (or its versions do not follow one
  * another); it has no seal, or its seal's key is not listed under its decider's name; its signature does not verify;
  * or the node's history as committed is not where its history now starts (a decision was taken out or changed).
  */
enum Uncounted:
  case NoDeciders, NotListed, NotVerified, Rewritten
