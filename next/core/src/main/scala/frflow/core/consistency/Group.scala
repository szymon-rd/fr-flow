package frflow.core.consistency

import frflow.core.name.{NodeId, SymbolName}

/** One consistency obligation (owner §15, §18). The bottom statements (no parts) and the premises are shown jointly
  * satisfiable; every statement above follows from its parts by a proven step (`complete`, `impl`), so it holds
  * wherever they do, and consistency is carried upward.
  */
enum Group:
  /** Bottom claims and the assumptions beside them that share open values (Declarations, and Definitions no proof
    * gives a meaning: tested Scala, or none): for every value provided where code runs meeting the assumptions about
    * it alone (`premises`), a meaning of each open one under which all of them hold. Proven code and fixed values
    * stand for their Definitions.
    */
  case Sharing(statements: List[NodeId], open: List[SymbolName], provided: List[SymbolName], witnesses: List[Witness],
      premises: List[NodeId])
  /** The premises of the groups over the same provided values, joined: some value of each, meeting what always holds
    * of it, meets them all together. Without it, premises that contradict each other would make every group taking
    * them hold for nothing.
    */
  case Premises(statements: List[NodeId], provided: List[SymbolName], witnesses: List[Witness])
  /** An `always(stored)` and what the state the store starts in meets (`stored.initially(…)`, an assumption): every
    * such state meets it, the first step of the rule that every state reached does.
    */
  case Start(statement: NodeId, start: Option[NodeId])

  def standing: Standing = this match
    case Sharing(_, _, _, ws, _) => Standing.of(ws)
    case Premises(_, _, ws)      => Standing.of(ws)
    case Start(_, s)          => s.fold(Standing.Unwitnessed(Nil))(_ => Standing.Witnessed)
