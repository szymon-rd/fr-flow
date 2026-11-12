package frflow.core.code

import frflow.core.name.SymbolName

/** What defines each Definition apart from the nodes: at most one attachment per Definition (checked against every
  * statement mentioning it). The
  * members of a structure given a class (`unclaimed`) have their code whether or not a statement mentions them: an
  * example may call one no claim speaks of. A structure whose class holds another has a word for what it holds
  * (`held`: that word, and the words of the held structure's members): a claim that reaches a structure through
  * its holder is proven from the claims on what is held, not from the class given for it.
  */
final case class CodeTable(attached: Map[SymbolName, Attachment], unclaimed: Set[SymbolName] = Set.empty,
    held: Map[SymbolName, Set[SymbolName]] = Map.empty)
