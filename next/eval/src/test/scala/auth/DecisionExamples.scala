package auth

import frflow.*

/** Today's examples of the decision, each setting the tables it is about: checked against the code in Scala only. */
class DecisionExamples extends FrFlowExamples(knowledge):
  private val aliceAt = grants := List(Grant(UserId("alice"), Path("/a")))
  private val aliceHolds = sessions := Sessions(List(Session("t1", UserId("alice"))))

  example("Alice's token and a grant for /a: she gets in", aliceAt, aliceHolds):
    admit("t1", Path("/a")) is Some(UserId("alice"))

  example("no grant for /b: refused", aliceAt, aliceHolds):
    admit("t1", Path("/b")) is None

  example("access without a grant is never given", aliceAt, aliceHolds):
    (admit("t1", Path("/b")) is Some(UserId("alice"))) is false

  example("a token that is not Alice's never acts for her", aliceAt, aliceHolds):
    (admit("t2", Path("/a")) is Some(UserId("alice"))) is false

  example("Alice with a grant for /a is not turned away", aliceAt, aliceHolds):
    (admit("t1", Path("/a")) is None) is false
