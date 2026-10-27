package frflow.api
package details

import frflow.ledger.CodeProof
import frflow.protocol.*
import io.circe.Codec

/** A node with everything around it: what `show` and the review read. `beside`: under each parent, the other
  * parts that with it make the parent; `keptBy`: for an invariant, the contracts that keep it (or are exempt);
  * `premises`: the assumptions it rests on; `trusted`: taken as true, unproven (an assumption); `tested`: its code is
  * tested against it, not proven (neither proven nor trusted);
  * `defs`: the Scala functions its formal statement calls, and those they call.
  */
final case class NodeDetails(node: Reviewed, isRoot: Boolean, trusted: Boolean, idea: String, parents: List[Reviewed],
    beside: List[(NodeId, List[Reviewed])], above: List[Reviewed], parts: List[Reviewed], designs: List[Reviewed],
    definitions: List[Reviewed], usedBy: List[Reviewed], calls: List[Reviewed], calledBy: List[Reviewed], keptBy: List[Reviewed],
    rivals: List[Reviewed], terms: List[Term], defs: List[DefText], codeProof: Option[CodeProof], diff: NodeDiff,
    premises: List[Reviewed] = Nil, tested: Boolean = false)
    derives Codec.AsObject
