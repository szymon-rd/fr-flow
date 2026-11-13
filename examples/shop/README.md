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

Each trait's companion holds the claims on it; `Shop.scala` assembles the tree. No trait has a member for a proof's
sake: `Inventory` is `reserve` and `release`, `Payments` is `charge`. A claim on a class made of others is said of
what those hold, reached through them: the checkout's claims speak of `warehouse.available`, `ledger.balance` and
`orders.registered` (the warehouse of its inventory, the ledger of its payments), and are proven from the claims on
the inventory, the payments and the order book, not from their classes.

Rocq proves all 50 claims (`bin/frflow shop check`, about 25 minutes from cold): 40 by FrFlow's tactic and ten
from proof files under `rocq/Proofs/Shop/`.

- **The stores and the services** (21 and 15 claims): by the tactic, but two of the payments' by hand. A
  service's claims are proven from the claims on its store, not from the store's class.
- **The checkout alone:** a new order in stock that its customer can cover is confirmed; a confirmed order is paid
  for, holds its units and is recorded; an order refused, for stock or for payment, leaves every product and
  every balance as it was (by the tactic); an order sent again is a duplicate and changes nothing (two proofs by
  hand: the first call registered the order, so the second does not win its registration).
- **Among other calls**, whatever they do between the steps of placing an order: no step leaves a product
  oversold or an account overdrawn that was not; no step adds to the postings of an order already charged, makes
  a posting of another order, undoes the claim of a payment, or leaves an order with postings whose payment is
  not claimed (the tactic, given more time than a check gives it). A step is a call of a service or of the order
  book, so `payments.charge` is one step here, though it is two transactions of the ledger.
- **Between the two transactions of one charge**, whatever other calls do there: no step of a charge makes a
  posting of another order or undoes a claim; and an order whose books are orderly is charged at most once, as
  long as the other calls make no posting of it in between. That last is what the charge takes of the others, said
  in the claim: its payment is claimed by this call, a claim is won once, and a call posts only for an order
  whose claim it won (`othersHonourClaims`, a design decision, not proven).
- **The forgetful checkout** confirms as the checkout does; the example shows what it leaves behind.

The five examples hold on the code, and Rocq shows each by running the code on the values it gives. Each of the
41 conditions the claims are stated under is shown possible, fifteen of them of values
`rocq/Proofs/Shop/Whole.v` gives.

Trusted: every order is for at least one unit and a positive amount (`ordersAreSensible`, the contract of
`Order`); each member of a store that changes it is one transaction (`storesAreTransactional`); and between the
two transactions of a charge no other call posts for its order (`othersHonourClaims`). Not covered: that last
shown of the other calls rather than taken of them (it needs who holds a claim said in the model), a crash between
two steps, liveness, stores behind an adapter.

```bash
sbt "testing/testOnly frflow.testing.ShopSuite"
```

```bash
sbt "project/Rocq/testOnly frflow.project.services.ShopRocqSuite"
```

```bash
bin/frflow shop check
```
