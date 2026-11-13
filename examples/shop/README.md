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

Rocq proves all 42 claims (`bin/frflow shop check`, about 16 minutes from cold): 38 by FrFlow's tactic and four
from proof files under `rocq/Proofs/Shop/`.

- **The stores and the services** (21 and 10 claims): by the tactic. A service's claims are proven from the claims
  on its store, not from the store's class.
- **The checkout alone:** a new order in stock that its customer can cover is confirmed; a confirmed order is paid
  for, holds its units and is recorded; an order refused, for stock or for payment, leaves every product and
  every balance as it was (by the tactic); an order sent again is a duplicate and changes nothing (two proofs by
  hand: the first call registered the order, so the second does not win its registration).
- **Among other calls:** no step of placing an order leaves a product oversold or an account overdrawn that was
  not, whatever other calls do between the steps (the tactic, given more time than a check gives it).
- **The forgetful checkout** confirms as the checkout does; the example shows what it leaves behind.

The five examples hold on the code. Rocq does not yet show them from the claims, and nine of the conditions the
claims are stated under are not shown possible (a witness is found for the others).

Trusted: every order is for at least one unit and a positive amount (`ordersAreSensible`, the contract of
`Order`), and each member of a store that changes it is one transaction (`storesAreTransactional`). Not restated
in this shape: that an order is charged once and that each step leaves other orders undisturbed, among other
calls; they need what a call takes of the others said in the claim. Not covered: a crash between two steps,
liveness, stores behind an adapter.

```bash
sbt "testing/testOnly frflow.eval.ShopSuite"
```

```bash
sbt "project/Rocq/testOnly frflow.project.services.ShopRocqSuite"
```

```bash
bin/frflow shop check
```
