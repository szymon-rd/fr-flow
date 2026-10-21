package frflow

import frflow.json.Json
import frflow.ledger.*

class JsonSuite extends munit.FunSuite:

  test("render and parse round-trip") {
    val j = Json.obj(
      "s" -> Json.str("quote \" backslash \\ newline \n unicode ⊢"),
      "n" -> Json.JNum(42),
      "a" -> Json.JArr(Seq(Json.JBool(true), Json.JNull, Json.obj())),
      "o" -> Json.obj("x" -> Json.JArr(Nil))
    )
    assertEquals(Json.parse(j.render()), j)
  }

  test("ledger round-trip") {
    val ledger = Ledger(
      Map(
        "T0" -> NodeEntry(
          Some(Approval("abc", "reviewer", "2026-01-01T00:00:00Z")),
          Some(
            CheckRecord(
              "def",
              Verification.Open,
              Seq(ObligationResult("init_Safe", ObligationStatus.Proven), ObligationResult("x", ObligationStatus.Open, "uses sorry")),
              Map("A.T0.invariant" -> Seq("propext")),
              Seq("message"),
              "2026-01-01T00:00:01Z"
            )
          )
        )
      )
    )
    assertEquals(Ledger.fromJson(Json.parse(ledger.toJson.render())), ledger)
  }
