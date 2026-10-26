package frflow.dsl.node

import frflow.core.spec.Statement

/** `examples` exists on every node with a promise (crm's and keycloak's assumptions about an operation use it);
  * `leftOpenAbove` on contracts only.
  */
class PromiseSyntaxSuite extends munit.FunSuite:
  test("examples on contracts on functions and flows, and on assumptions about an operation") {
    assert(summon[OnPromise[Statement.Contract]] != null)
    assert(summon[OnPromise[Statement.FlowContract]] != null)
    assert(summon[OnPromise[Statement.AssumedCall]] != null)
  }

  test("leftOpenAbove on contracts only") {
    assert(summon[OnContract[Statement.FlowContract]] != null)
    assert(compileErrors("summon[OnContract[Statement.AssumedCall]]").nonEmpty)
  }
