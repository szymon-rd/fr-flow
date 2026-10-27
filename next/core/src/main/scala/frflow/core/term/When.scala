package frflow.core.term

/** One arm of a match over `S`: when the value is case `C`, the case's variable and the arm's body, a host function
  * over the case's term (LNCS 7470 §3.2), which reads the case's fields by selector.
  */
final case class When[T[_], S, C, R](c: Case[S, C], x: Bound[C], body: T[C] => T[R])
