package frflow.api.view

import frflow.core.name.RelPath

/** What listing the first decider did: the deciders' list written (commit it: only committed versions count), or a
  * list is there already (a later version is signed by a key the one before lists, never written over).
  */
enum Listed:
  case Written(file: RelPath)
  case Already(file: RelPath)
