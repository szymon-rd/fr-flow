# Links: a link shortener, its three members, and how they relate

A link shortener gives a URL a short code, tells where a code leads, and removes a code. Each member has a contract,
and most of what matters is how the members relate:

- the code a URL is given leads to it;
- shortening a URL again gives the same code and changes nothing;
- shortening never moves a link that already leads somewhere;
- a removed code leads nowhere, and no other code moves;
- a removed code is not given again, so an old printed link never starts leading somewhere new.

This example writes the shortener as ordinary Scala and has Rocq prove each of these of the class.

## The interface

A trait with the members such a service has, and nothing added for the proofs:

```scala
trait Links extends Mutable:
  update def shorten(url: Url): Code
  def resolve(code: Code): Option[Url]
  update def remove(code: Code): Unit
```

`resolve` is not `update`, so it changes nothing: its trait already says so, and no claim needs to.

## The claims

The claims are in the trait's companion (`src/main/scala/links/Links.scala`), written through the members of
`shortener`, the `Declaration` of the trait:

```scala
val shortenIsIdempotent = Node.claim("Shortening a URL a second time gives the code it gave the first time and " +
    "changes nothing.")(
  forall((u: Term[Url]) => shortener.shorten(u).isIdempotent))

val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
  forall((u: Term[Url]) => shortener.shorten(u).andThen(code => shortener.resolve(code)) === some(u)))

val shortenKeepsExistingLinks = Node.claim("Shortening never changes where a code that leads somewhere leads.")(
  forall((u: Term[Url], c: Term[Code]) =>
    shortener.resolve(c).isDefined implies shortener.resolve(c).unchangedBy(shortener.shorten(u))))

val removeChangesOnlyThatCode = Node.claim("Once a code is removed, every code leads where it led before, but " +
    "the removed one, which leads nowhere.")(
  forall((c: Term[Code], d: Term[Code]) =>
    shortener.resolve(d).following(shortener.remove(c)) ===
      when(d === c)(none[Url]).otherwise(shortener.resolve(d))))

val removedCodeLeadsNowhere = Node.claim("A removed code leads nowhere.")(
  forall((c: Term[Code]) => shortener.resolve(c).following(shortener.remove(c)).isEmpty))

val removeKeepsOtherCodes = Node.claim("Removing a code changes where no other code leads.")(
  forall((c: Term[Code], d: Term[Code]) =>
    (c =!= d) implies shortener.resolve(d).unchangedBy(shortener.remove(c))))

val removedCodeNotReissued = Node.claim("A code just removed is not given to the next URL shortened.")(
  forall((c: Term[Code], u: Term[Url]) => shortener.shorten(u).following(shortener.remove(c)) =!= c))
```

`removeChangesOnlyThatCode` says what removing does, exactly; its two cases, `removedCodeLeadsNowhere` and
`removeKeepsOtherCodes`, are its parts, and Rocq proves it from them.

### The calls, shortened

A call in a claim is made on the structure as it stands; `.in(state)` makes it on another state and `.after` is the
state it leaves. The claims above use shorthands for what the calls say of each other, each built of `.in` and
`.after` (`modules/dsl/src/main/scala/frflow/dsl/structure/Call.scala`), so Rocq is given the same as it would be
for the long form:

| Written | Is | Says |
|---|---|---|
| `q.following(c)` | `q.in(c.after)` | `q`, once `c` has been made |
| `c.again` | `c.in(c.after)` | the same call a second time |
| `c.andThen(r => d(r))` | `d(c).in(c.after)` | `d`, given what `c` gives, once `c` has been made |
| `c.changesNothing` | `c.after === ` the state `c` is made on | the call leaves the structure as it found it |
| `q.unchangedBy(c)` | `q.following(c) === q` | `c` does not change what `q` gives |
| `c.isIdempotent` | `(c.again === c) && (c.again.after === c.after)` | made again, it gives what it gave and changes nothing |

Only the call they are applied to is moved: a call written among its arguments is made where it was written.

## The class

```scala
final class RetiringLinks(var issued: List[Link], var retired: List[Code]) extends Links:
  update def shorten(url: Url): Code =
    val held = issued
    val known = held.find(l => Issued.leadsTo(held, l.code) == Some(url)).map(l => l.code)
    val code = known.getOrElse(Code(Issued.above(held, retired)))
    if known.isEmpty then issued = Link(code, url) :: held
    code

  def resolve(code: Code): Option[Url] = Issued.leadsTo(issued, code)

  update def remove(code: Code): Unit =
    issued = issued.filter(l => l.code != code)
    retired = code :: retired
```

A claim holds of the structure in every state, not only in those the class reaches from an empty one. That is what
shapes the class:

- `shorten` gives again only a code that leads to the URL (the first link of that code), not any link of the URL:
  in a state with two links of one code, the second does not lead anywhere.
- A new code is a number above every code given and every code removed (`Issued.above`), not a counter, which a
  state could hold below a code already given.
- `remove` keeps the code among those removed, so it is never above the next number again.

## What Rocq proves

`bin/frflow links check`:

```text
+ removedCodeLeadsNowhere: proven
+ removeKeepsOtherCodes: proven
+ shortenIsIdempotent: proven
+ shortenedCodeResolves: proven
+ shortenKeepsExistingLinks: proven
+ removeChangesOnlyThatCode: proven
+ removedCodeNotReissued: proven

Shown possible
  condition 1 of shortenKeepsExistingLinks can hold: proven
  condition 1 of removeKeepsOtherCodes can hold: proven

Examples
  + a new URL: a new code, which leads to it, and code 0 still leads home  Rocq: shown
  + a URL shortened again: its code, and nothing changed  Rocq: shown
  + a removed code: it leads nowhere, and is not given again  Rocq: shown
```

Each claim is proven of the class by a proof by hand in `rocq/Proofs/Shortener`: what they need is induction over
the list of links (what a find gives, what filtering out a code leaves, that the new number is above every code),
which FrFlow's tactic does not do. The shared lemmas are in `Lemmas.v`; each claim's proof is a few lines over them.
No node is decided yet: the claims are the developer's to accept (`bin/frflow links review --as NAME`).

### How a change is caught

The class forgets to keep the codes it removes:

```diff
   update def remove(code: Code): Unit =
     issued = issued.filter(l => l.code != code)
-    retired = code :: retired
```

The shared lemma that says what removing leaves no longer holds of the code, so no proof resting on it goes
through, and the third example fails on the code: removing code 0 and shortening a URL gives code 0 again.

```text
o removedCodeNotReissued: open
  not proven: it imports the shared lemmas, which are not proven (the error is theirs, not its own proof's)
    Proofs/Shortener/Lemmas.v:87: Lemmas_remove: In environment
…
Examples
  x a removed code: it leads nowhere, and is not given again  Rocq: the claims contradict it; the code does not hold it
```

## What is not modelled

- Other callers. The claims are on one call at a time; nothing is said of two calls whose steps interleave
  (`amongOthers`), and the class keeps its state in memory.
- "Never given again" at any later time. `removedCodeNotReissued` says the next code given is not the removed one;
  that it holds after any number of calls needs a member the claims can ask (whether a code was removed), which the
  interface does not have.
- What a code looks like (letters, length), and whether a URL is well formed.

## Running it

```sh
bin/frflow links check        # prove the claims, run the examples on the code and in Rocq
bin/frflow links status       # the tree, the summary and the warnings
```

`LinksSuite` (`sbt testing/test`) checks the model is valid and its examples hold of the code; `LinksRocqSuite`
(`sbt "project/Rocq/testOnly frflow.project.services.LinksRocqSuite"`) checks it whole in Rocq.
