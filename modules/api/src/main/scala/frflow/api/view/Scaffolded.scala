package frflow.api.view

import frflow.core.name.RelPath

/** What `scaffold` did with a node's proof file: stubs written to it (created if missing); or nothing to add (every
  * obligation left open already has its lemma there).
  */
enum Scaffolded:
  case Written(file: RelPath)
  case NothingToAdd
