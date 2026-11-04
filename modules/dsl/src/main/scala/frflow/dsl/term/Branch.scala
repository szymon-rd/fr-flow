package frflow.dsl.term

import frflow.core.term.Case

/** One arm of a match as the developer wrote it (`.on[Case](fields => …)`): the case, its variable's name and type,
  * and the arm as a function of the case's term (its fields read by selector), built by `CaseMacros.branch`.
  */
final case class Branch[S, C, R](c: Case[S, C], hint: String, caseType: LeanType[C], body: Term[C] => Term[R])
