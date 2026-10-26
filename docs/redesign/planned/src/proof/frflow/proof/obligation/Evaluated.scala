package frflow.proof.obligation

import frflow.core.name.{DefName, NodeId}

/** What is evaluated: a promise's post on the call (`eval_i`, `probe_j`), or the proven code on the inputs. */
enum Evaluated:
  case Post(node: NodeId)
  case Code(define: DefName)
