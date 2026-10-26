# Rooms

Booking meeting rooms: the example in the top-level README.

- `src/main/scala/rooms/Knowledge.scala` holds the root, `GrantWhenFree`, stated over moments, and the contract on
  `granted`, `GrantWhenNoOverlap`, stated over start and end times.
- `lean/Proofs/Rooms/GrantWhenFree.lean` proves the root from the contract.
- `src/main/scala/rooms/Calendar.scala` is the code. It checks a request against its neighbours in start order, and is
  tested against the contract on generated cases.

```sh
bin/frflow rooms tree
bin/frflow rooms check
bin/frflow rooms status
```
