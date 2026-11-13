# Shop: a checkout across three services

An order checkout: it registers the order, reserves the stock, charges the customer and records how the order
ended; when the payment does not go through it releases the stock. It is the example of a service that calls
other services, each over a store of its own, and is proven from their claims. Like
[the payments example](../payments/README.md), each piece is a structure: a `Declaration` of a trait, given a
class FrFlow reads.

```scala
final class ShopCheckout(inventory: Inventory^, payments: Payments^, orders: OrderBook^) extends Checkout:
  update def place(o: Order): Placement = …
```

| Trait | Class | What it does |
| --- | --- | --- |
| `Warehouse`, `Ledger`, `OrderBook` | `MovementWarehouse`, `PostingLedger`, `JournalOrderBook` | the stores: `hold`, `putBack`; `claim`, `chargeIfCovered`; `register`, `settle` |
| `Inventory`, `Payments` | `WarehouseInventory`, `LedgerPayments` | services, each over one store: `reserve`, `release`; `charge` |
| `Checkout` | `ShopCheckout` | the service over the two services and the order book: `place` |
| `ForgetfulCheckout` | `NoReleaseCheckout` | the checkout without the release: it confirms as `Checkout` does, and leaves stock held |

Each trait's companion holds the claims on it; `Shop.scala` assembles the tree. A claim on a class made of others
is said through what those expose: the checkout's claims speak of `inventory.available`, `payments.balance` and
`orders.registered`, and are proven from the claims on the inventory, the payments and the order book, not from
their classes.

Rocq proves the 21 claims on the stores and the 7 on the two services by FrFlow's tactic, and 5 of the 7 claims
on the checkout alone (a new order in stock that its customer can cover is confirmed; a confirmed order is paid
for, holds its units and is recorded; an order refused leaves every product and every balance as it was). The two
about an order sent again (it is a duplicate, and changes nothing) are proven by hand under `rocq/Proofs/Shop/`. The forgetful checkout's one claim and the five examples (the
unit it leaves held among them) hold on the code.

Trusted: every order is for at least one unit and a positive amount (`ordersAreSensible`, the contract of
`Order`). Not covered yet in this shape: the claims over every step of placing an order among other calls (no
product oversold, no account overdrawn, an order charged once), which the shape before structures stated and
proved in Lean; a crash between two steps; liveness; stores behind an adapter.

```bash
sbt "testing/testOnly frflow.eval.ShopSuite"
```

```bash
bin/frflow shop check
```
