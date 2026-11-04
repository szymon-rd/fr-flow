package frflow.api.view

import frflow.core.name.RelPath

/** What `scaffold` did with a node's proof file: stubs written to it (created if missing); nothing to add (every
  * obligation left open already has its theorem there); or stubs not added, since the file's closing `end` of its
  * namespace is not found.
  */
enum Scaffolded:
  case Written(file: RelPath)
  case NothingToAdd
  case EndNotFound(file: RelPath)
