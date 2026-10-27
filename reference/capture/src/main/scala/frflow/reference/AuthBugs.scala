package frflow.reference

import _root_.auth.*

/** auth's seeded bug, as `AuthSuite` seeds it. */
object AuthBugs:
  private val alice = UserId("alice")
  private val report = Path("/reports/q3")
  private val grantTable = List(Grant(alice, report))
  private val tokens = Map("t-1" -> alice)

  def all: List[Seeded] =
    val careless: (String, Path) => Option[UserId] = (t, _) => tokens.get(t)
    val onSessions = knowledge.implementTested(decisionContract)((t, _) => sessions.value(t))
    List(Seeded("careless decision code", inTable = true,
      "decisionContract implemented by (token, _) => the user the token was issued to: the grant table ignored",
      "AuthSuite: an implementation that ignores the grant table is stopped by its contract, and fails a generated " +
        "case",
      Stops.onCall(
        """decide("t-1", Path("/admin")), grants = List(Grant(alice, /reports/q3)), tokens = t-1 -> alice""") {
        knowledge.implementTested(decisionContract)(careless)
          .service(decisionContract)(grants.bind(grantTable), sessions.bind(t => tokens.get(t)))("t-1", Path("/admin"))
      } ++ Stops.generated(onSessions, decisionContract) ++ Stops.examples(onSessions, decisionContract)))
