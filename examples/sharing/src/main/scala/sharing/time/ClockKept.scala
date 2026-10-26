package sharing.time

import frflow.*

/** The clock, as the service's flows see it (FrFlow's `Clock` boundary and `ClockModel`). */
object ClockKept:
  val clockKept = Node.assumption(Clock.boundary)(ClockModel)("The clock gives the time now, in seconds; a sleep moves it on by the time asked and by a delay it may add, never less, and nothing else moves it while a flow runs.",
    why = "Q9: the server's clock, in seconds, read once per request and once per run of housekeeping. Steps take no time (the synchronous hypothesis), so a request answers at one moment. The fake clock, used in tests, is tested against this model; the computer's clock (SystemClock) is assumed to keep it.",
    idea = "Time and housekeeping")
    .implementedBy(c => FakeClock(c), _.state)
