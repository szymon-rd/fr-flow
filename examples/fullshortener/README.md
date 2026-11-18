# Full shortener: a link shortener, from its promises down

The link shortener of `examples/links`, with the same interface and the same class, stated from the top: four
promises to whoever holds a link, two of them proven from what the members do, and what the members do proven of
the class.

```text
A link leads to its URL until it is removed.
  Shortening a URL never changes where an existing code leads.
  Removing a code never changes where any other code leads.
The code a URL is given leads to that URL.
A removed link never leads anywhere again.
  A removed code leads nowhere.
  A removed code is never given to a URL again.
  Shortening a URL changes where no code leads but the one it gives.
  Removing a code never changes where any other code leads.
  (design) A new code is a number above every code given and every code removed, so no code is given twice.
Shortening a URL again gives the same link and changes nothing.
```

## The interface

```scala
trait Links extends Mutable:
  update def shorten(url: Url): Code
  def resolve(code: Code): Option[Url]
  update def remove(code: Code): Unit
```

## The promises

The roots are in `src/main/scala/fullshortener/FullShortener.scala`. A claim holds from any state:

- **A link leads until removed** (`linkLeadsUntilRemoved`): a code that leads to a URL still leads to it after any
  calls made later (`later: shortener.History`), as long as removing that code is not among them. It is proven from
  its two parts by induction over those calls: each is a URL shortened, which moves no existing code, or another
  code removed, which moves no other.
- **A link works when given** (`shortenedCodeResolves`): proven of the class directly.
- **A removed link stays removed** (`removedLinkStaysRemoved`): once a code is removed, it leads nowhere after any
  calls made later. Proven by induction over those calls from four parts: removing leaves it leading nowhere, no
  later URL is given it, shortening moves no code but the one it gives, and removing another code moves no other.
- **The same link again** (`shortenIsIdempotent`): proven of the class directly.

The two shortening claims are not one said twice. "Never changes where an existing code leads" is what stops a new
URL from taking a code that is in use; "changes where no code leads but the one it gives" is what keeps a code that
leads nowhere leading nowhere. A shortener with one code for every URL meets the second and not the first.

## What Rocq proves

`bin/frflow fullshortener check`: the claims on the members are proven of the class by hand
(`rocq/Proofs/FullShortener`, over lemmas taken from `examples/links`), the two promises with parts are proven
from their parts alone (one condition is shown possible by values given in `Whole.v`), and the three examples are shown from the claims.

### How a change is caught

The class forgets to keep the codes it removes:

```diff
   update def remove(code: Code): Unit =
     issued = issued.filter(l => l.code != code)
-    retired = code :: retired
```

One claim on the members goes open, `removedCodeNotReissued` (with the lemmas on a removed code it rests on), and
the third example fails on the code (removing code 0 and shortening a URL gives code 0 again); the other claims on the members stay proven. The roots are then all reported
open, those that do not rest on that claim as well: FrFlow proves the roots of the code together (`root_impl`).

## What is not modelled

- A history of a structure with a member that takes more than one input: `History` reads one input a member.
- Other callers: nothing is said of two calls whose steps interleave, and the class keeps its state in memory.
- What a code looks like, and whether a URL is well formed.

## Running it

```sh
bin/frflow fullshortener check        # prove the claims, run the examples on the code and in Rocq
bin/frflow fullshortener status       # the tree, the summary and the warnings
```
