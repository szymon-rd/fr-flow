# Shop: a checkout across three services

An order checkout: it registers the order, reserves the stock, charges the customer and records how the order
ended; when the payment does not go through it releases the stock. It is the example of a service that calls
other services, each over a store of its own, and is proven from their contracts.
[The payments example](../payments/README.md) writes services another way: each a structure, a `Declaration` of a
trait defined by a class.

```scala
final class Checkout(inventory: Inventory^, payments: Payments^, orders: OrderBook^):
  def place(o: Order): Placement = …
```

| Piece | Kind | What it does |
| --- | --- | --- |
| `Warehouse`, `Ledger`, `OrderBook` | stores | `hold`, `putBack`; `claim`, `chargeIfCovered`; `register`, `settle` |
| `Inventory`, `Payments` | services, each over one store | `reserve`, `release`; `charge` |
| `Checkout` | service over the two services and the order book | `place` |
| `Forgetful` | the checkout without the release | answers as `Checkout` does, and leaves stock held |

Each class's companion holds its contracts; `Shop.scala` assembles the tree. Lean proves all 40 claims, 28 by
FrFlow's tactic and 12 by hand under `lean/Proofs/Shop/`:

- **Alone:** a new order in stock that its customer can cover is confirmed; a confirmed order is paid for, holds
  its units and is recorded; an order refused, for stock or for payment, leaves every product with what it had
  and no posting; an order sent again is a duplicate and changes nothing.
- **Among other calls:** no product is oversold and no account overdrawn at any step; no step adds to the
  postings of an order already charged; each step grants other orders what the checkout relies on of them.

The seven examples hold in the evaluator and in Lean. One is the race for the last unit: another order takes it
between two steps of this one, which is then answered out of stock with nothing oversold. Another is `Forgetful`
leaving a unit held after a payment is refused.

Trusted, as design nodes: each store's method is one transaction, and every other caller is a service that keeps
what the checkout is proven to keep. Not covered: a crash between two steps, liveness, stores behind an adapter.

```bash
sbt "testing/testOnly frflow.eval.ShopSuite"
```

```bash
sbt "project/Lean/testOnly frflow.project.services.ShopLeanSuite"
```

```bash
bin/frflow shop check
```
