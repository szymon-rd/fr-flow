package auth

import frflow.*

/** An example that sets the value of a provided Definition (`grants := …`): checked against the code in Scala only
  * (Lean is not asked it), and shown so.
  */
class AuthExamples extends FrFlowExamples(knowledge):
  example("a grant for Alice's path admits her session", grants := List(Grant(UserId("alice"), Path("/a")))):
    admits(Session("t1", UserId("alice")), Path("/a")) is true

val authExamples = AuthExamples()
