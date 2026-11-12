# Ox, proven in Rocq against the JDK's contracts

Work in progress. The aim: that no fork outlives its scope ("containment"), proven of Ox 1.1.0's code as it is
compiled, for every client and any nesting of scopes, from contracts on the JDK's classes and nothing else.

## The files, in the order they are compiled

Library (`modules/proof/rocq/FrFlow/Threads/`, logical path `FrFlow.Threads`):

| File | What it is |
|---|---|
| `Prog.v` | A program: returns, calls one operation of a library (`Vis`), loops (`Iter`), calls a closure (`Call`). |
| `Jdk.v` | The assumptions. Each JDK class Ox uses: its state, and a contract per method (`opstep`). |
| `Sem.v` | Threads: a configuration, and one thread's step at a time, in any order. |
| `Logic.v` | `wp`: an invariant, ghost state, a rely; one rule per kind of step. `sound`: no axioms. |
| `Lang.v` | What Scala's constructs are read as (`bind`, `try_catch`, `try_finally`, `loop`, `while`, traversals). |

Ox (`examples/ox/rocq/Ox/`, logical path `Ox`):

| File | What it is |
|---|---|
| `Code.v` | Ox's scopes and forks as programs. Written by hand; the generator (in progress) must reproduce it from TASTy. |
| `Ghost.v` | The ghost state, the invariant `Inv`, the rely `Rely`. |
| (to come) | The specifications of the closures, the proof of each method, the theorem. |

Compile from the repository root:

```bash
for f in Prog Jdk Sem Logic Lang; do rocq compile -Q modules/proof/rocq/FrFlow FrFlow modules/proof/rocq/FrFlow/Threads/$f.v; done
```

```bash
for f in Code Ghost; do rocq compile -Q modules/proof/rocq/FrFlow FrFlow -Q examples/ox/rocq/Ox Ox examples/ox/rocq/Ox/$f.v; done
```

## The theorem aimed at

For every client whose closures keep to the precondition below: in every configuration reached from the first
thread running the client, by any order of the threads' steps, once the first thread has ended, no other thread
has an operation left (each thread's remaining program is `Ret`).

The client's precondition (confinement): a closure given to `fork` on a scope captures only that scope's
capability and those of scopes enclosing it. Lexical scoping does not give this: `fork(using outer) { fork(using
inner) { … } }` type-checks and Ox's run-time check passes it.

## The design of the proof

- **Ghost state** (`Ghost.v`). Per herd (named by the reference of its `threads` set): owner, `h_exited` (its
  closing loop has found the set empty), `h_parent` (the herd it was opened inside), `h_stamp`. Per thread:
  `g_role` (`Main`, `Created t th b`: made by `t`, not yet in a set; `ForkOf h b`: in herd `h`'s set or once in
  it), `g_removed` (it has run its `threads.remove`), `g_open` (the herds it owns that are not exited, innermost
  first). `g_fin`: the references that hold a scope's finalizers.
- **Where the ghost state changes.** `TsNew` (in `ThreadHerd_new`): the herd is registered, owner the caller,
  parent the head of the caller's `g_open` or else the herd the caller is a fork of, pushed on the caller's
  `g_open`. `NewThread`: role `Created`. `TsAdd`: role `ForkOf`. `TsRemove` by the fork itself: `g_removed`.
  `TsIsEmpty` answering `true` in the closing loop: `h_exited`, popped from `g_open`. `ArNew`: `g_fin`.
- **Inside.** `anc Γ h h'`: `h'` is `h` or an ancestor by `h_parent`. `inside Γ u h`: `u` is an unremoved fork of
  some `h0`, or owns an open `h0`, with `anc Γ h0 h`. Key lemma: `Inv σ Γ -> inside Γ u h -> h` is not exited.
  It is what `TsAdd` needs (a thread added to an exited herd would break `i_exit`), and it is stable for `u`
  (its own role, flags and open herds; parent links never change).
- **Preconditions.** `startThread` on herd `h` by `t`: `inside Γ t h`, and for the body `b` every capability it
  captures is well formed with `anc Γ h (its herd)`. A closure called by `t`: `t` is not removed, and every
  capability it captures or is given is well formed with `t` inside its herd.
- **Postconditions.** A call of a closure, and every method but those that open or close a herd, leaves the
  ghost state as another thread's step could have (`Rely t Γ Γ'`), so what the caller knew stays.
  `scopedWithCapability` pops the herd it is given, in both outcomes.
- **Most of the code touches nothing the invariant reads** (futures, counters, the thread-local, `ErrorMode`):
  it is dispatched by one lemma over a syntactic class of programs (`frameonly`), not operation by operation.
- **The end.** `Active t Γ := g_removed Γ t = false` is required at every step that is not a thread's end, so a
  removed thread's program is `Ret`. When the first thread has ended it owns no open herd (`i_done`); then no
  fork is unremoved, by descent on `h_stamp` along owners.

## What is assumed

`Jdk.v`, read in full: each contract is an assumption. Two are stronger than the JDK's documentation or rest on
the reference implementation: `TsIsEmpty` (exact at one moment), and that the JVM's type safety makes the casts
the compiler inserted succeed (`TypeError` has no step). Not modelled: integer overflow, `Thread.stop`, errors
of the JVM, a `Throwable`'s identity and suppressed list. `ErrorMode` and `ForkLocalMap` are not read: their
methods are taken to touch nothing of the JDK state here (`Extern`). `uninterruptible` inside `runFinalizers`
is not read (`Chaos`): the proof must show it unreachable, which holds for clients that register no finalizer.
