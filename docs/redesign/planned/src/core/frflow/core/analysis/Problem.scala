package frflow.core.analysis

import frflow.core.name.{NodeId, SymbolName, TypeName}
import frflow.core.spec.NodeKind

/** What keeps a theory from being checked: each case names what is wrong and where. */
enum Problem:
  // The graph
  case DuplicateId(id: NodeId)
  case NoRoot
  case SeveralRoots(roots: List[NodeId])
  case AboveItself(id: NodeId)
  case ParentOutside(id: NodeId, parent: NodeId)
  case PromiseWithoutParent(id: NodeId, kind: NodeKind)
  case DesignWithoutParent(id: NodeId)
  case UnderDesign(id: NodeId, design: NodeId)
  case UnderDefinition(id: NodeId, definition: NodeId)
  // The vocabulary
  case DefinedTwiceIn(definition: NodeId, symbol: SymbolName)
  case DefinedThroughItself(definition: NodeId)
  case DefinesAnOperation(definition: NodeId, op: SymbolName)
  case ExistsOverBoundedInt(definition: NodeId, sort: TypeName)
  case ReservedName(name: String)
  case DeclaredTwice(name: String)
  case CodeOnlyInStatement(id: NodeId, symbol: SymbolName)
  // Invariants, examples and code
  case NotKeptInScope(invariant: NodeId, node: NodeId)
  case NoKeeper(invariant: NodeId)
  case ExemptWrongKind(node: NodeId, invariant: NodeId)
  case NamedTwice(node: NodeId, invariant: NodeId)
  case ExemptWithoutReason(node: NodeId, invariant: NodeId)
  case ScopeOutside(invariant: NodeId, scope: NodeId)
  case ExampleArity(id: NodeId, example: Int, expected: Int)
  case DataForCodeOnly(id: NodeId, symbol: SymbolName)
  case FlowFailsUnstated(contract: NodeId)
  case ProvenFlowTakesOutsideStep(contract: NodeId)
  case CodeWithoutPromise(id: NodeId)
