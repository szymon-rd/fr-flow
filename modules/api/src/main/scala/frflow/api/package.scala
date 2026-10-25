package frflow.api

// The ledger's types a front end reads, so it imports only this package and the protocol's.
export frflow.ledger.{CodeProof, Decide, Found, Mention, Mentioned, Refusal}
export frflow.check.Progress

// A node with what is around it, and what changed since it was decided.
export frflow.api.details.{CodeChange, Details, DiffLine, FieldChange, Fields, GoneNode, LineDiff, MovedAbove, NodeDetails,
  NodeDiff, Term}

// What the reads and the operations return.
export frflow.api.report.{CheckReport, CheckedNode, CiReport, FailingExample, Inbox, Overview, Queued, Rendered, Scaffolded,
  StatusReport, Tree, TreeNode, Trees}
