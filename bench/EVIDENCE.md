# Evidence plan

What would show FrFlow keeps a large agent-built system's theory, and what it costs. Measured
so far: `bench/generate.py` (speed at 401 nodes, README), `examples/crm` (a seeded SQL bug stopped
by a port's check; checks at about 1% of a request), and the translation tests (an injected `≥`→`>`
bug the examples miss is found by probes, `LeanSuite`).

## Trial

One real service, built over four weeks by agents with one or two developers deciding, against a
control built the same way without FrFlow (same idea, same agents, same tasks).

Tasks: the initial build, then ten change requests written in advance, three of them touching a
rule stated once and relied on elsewhere (the drift FrFlow is for).

## Measures

| question | measure |
|---|---|
| Is drift caught? | Seeded faults (twenty: dropped checks, widened queries, a rule broken in one of three places), share found before merge, in each arm |
| Is the theory kept? | After each change, a developer new to the project answers ten "why is it so" questions from the repository alone; answers graded against the original developer's |
| What does it cost the developer? | Decisions per change, and minutes spent deciding (`Decisions.load`, browser timestamps) |
| What does it cost the agent? | Tokens and wall time per change, each arm |
| What does it cost CI? | `ci` time per change (cold and cached) |
| False alarms | Nodes sent to review that the developer accepted unchanged, as a share of reviews |
| Translation | Probes and examples evaluated per contract; disagreements found (each one a bug in FrFlow) |

## Stop rule

If deciding takes more than a fifth of the developer's time, or false alarms exceed half of the
reviews, the trial reports that, and what caused it, before going on.
