"""Generates examples/scale: a synthetic knowledge base on the DAG of refinements (docs/DAG.md), to
measure how FrFlow behaves as a project grows. No statement grows with the project: each node says
one thing in words the vocabulary defines, and has at most six parts.

One root, `Catalog`: every service shows a reader the visible values of each request (within its
bounds), and never a value under the reader's floor; in one defined word, `catalogOk`, over the
groups' words (or the areas', past twenty-five services). Its parts:

  Group{k}          services 5k to 5k+4 serve their requests and never show a value under the floor
                    (`group{k}Ok`, defined by `Group{k}Terms` over those five services); its parts are
                    the five services and `Floor{k}`, the invariant their five contracts keep;
  Area{k}           groups 5k to 5k+4 (`area{k}Ok`), when there are more than five groups.

Each service `Service{i}` is a claim with two or three granular parts, proven by one contract
`Show{i}` on its operation `serve{i}`, with proven code. Two kinds alternate: an open service
(shows every visible value; parts FromRequest, AllVisible) and a bounded one (shows the visible
values within a shared limit; parts FromRequest, WithinLimit, AllVisible). Every fifth service's
code calls the previous service's operation (proven from that one's contract). In every other
group, the two bounded services share one claim (`WithinLimit{a}And{b}`): a node with two parents.
Every tenth service's `complete` is proven by hand (lean/Proofs).

The vocabulary, decided once: `visible` (definition `Clearance`), `limit` (definition `Limit`) and
`serves` (definition `Serving`) in `Vocabulary.scala`; the groups', areas' and catalog's words in
`Groups.scala`.

    python3 bench/generate.py 20      # about a hundred nodes
    python3 bench/generate.py 60      # about three hundred
    sbt "scale/run check"             # cold, then after one change; sbt "scale/run status"
"""
import os, sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.join(here, "..", "examples", "scale")
src = os.path.join(root, "src", "main", "scala", "scale")
proofs = os.path.join(root, "lean", "Proofs", "Scale")
for d in (src, proofs):
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))

L = "List[BigInt]"
lower = lambda s: s[0].lower() + s[1:]


def write(path, text):
    with open(path, "w") as f:
        f.write(text)


def bounded(i):
    """The kinds alternate (open, bounded), with the services that call another always bounded."""
    return i % 5 in (0, 2)


def calls(i):
    return i > 0 and i % 5 == 0


def pair_first(i):
    """Bounded services 5k and 5k+2 of every other group share their WithinLimit claim."""
    return i % 10 == 5 and i + 2 < n


def shared_by(i):
    if pair_first(i):
        return i
    if i % 10 == 7 and pair_first(i - 2):
        return i - 2
    return None


def within_id(i):
    s = shared_by(i)
    return f"WithinLimit{s}And{s + 2}" if s is not None else f"WithinLimit{i}"


def served(i):
    """What service i promises its readers, in the vocabulary (over xs, f)."""
    req = "xs.filter(x => x <= limit.value)" if bounded(i) else "xs"
    return f"serves({req}, f, serve{i}(xs, f))"


# ---------------------------------------------------------------------------------------------
# The vocabulary, decided once, with the operations (each service's): a file of its own, so that
# files do not initialize each other in a cycle
# ---------------------------------------------------------------------------------------------
write(os.path.join(src, "Vocabulary.scala"), f"""package scale

import frflow.*

// The ubiquitous language of the catalog: what a reader may see, the bound, and what serving means.

val visible = Param[(BigInt, BigInt) => Boolean]("visible", "whether a value may be shown to a reader whose floor is the second")
val limit   = Param[BigInt]("limit", "the largest value a bounded service may show")
val serves  = Param[({L}, BigInt, {L}) => Boolean]("serves",
  "whether a result serves a request's values to a reader with the given floor: nothing from elsewhere, every visible value")

val clearance = Node.definition("Clearance", "A value may be shown to a reader when it is not under the reader's floor.",
  why = "The floor is the reader's clearance: what is at or over it they may see."
)(visible := ((x: BigInt, f: BigInt) => x >= f))

val limits = Node.definition("Limit", "Bounded services show no value over one thousand.",
  why = "Values over the limit are for the services that are not bounded."
)(limit := BigInt(1000))

// What each service shows: an operation, implemented by the service's code.
""" + "".join(f'val serve{i} = Param[({L}, BigInt) => {L}]("serve{i}", "what service {i} shows of a request\'s values to a reader with the given floor")\n'
              for i in range(n)) + f"""
val serving = Node.definition("Serving", "A result serves a request when it holds only the request's values, and every one the reader may see.",
  why = "Serving is the promise every service makes; stated once so that every service means the same by it."
)(serves := ((xs: {L}, f: BigInt, r: {L}) => r.forall(x => xs.contains(x)) && xs.forall(x => visible(x, f) ==> r.contains(x))))
""")

# ---------------------------------------------------------------------------------------------
# The groups and areas: each a word of the vocabulary over at most five services (or groups), so
# that no statement grows with the project
# ---------------------------------------------------------------------------------------------
def ok(i):
    """What service i promises with the floor (over xs, f): it serves, and shows nothing under the floor."""
    return f"{served(i)} && serve{i}(xs, f).forall(x => visible(x, f))"


groups = [(f"Group{k // 5}", list(range(k, min(k + 5, n)))) for k in range(0, n, 5)]
group_of = {i: gid for gid, svcs in groups for i in svcs}
tiers = [[(gid, svcs, [f"Service{i}" for i in svcs]) for gid, svcs in groups]]
while len(tiers[-1]) > 5:
    below = tiers[-1]
    tiers.append([(f"Area{k // 5}", [s for c in below[k:k + 5] for s in c[1]], [c[0] for c in below[k:k + 5]])
                  for k in range(0, len(below), 5)])
parent_of = {p: gid for tier in tiers for gid, _, parts in tier for p in parts}
top = [gid for gid, _, _ in tiers[-1]]
for gid in top:
    parent_of[gid] = "Catalog"


def word(gid):
    return lower(gid) + "Ok"


def floor_id(gid):
    return "Floor" + gid[len("Group"):]


words, definitions, claims = [], [], []
for t, tier in enumerate(tiers):
    for gid, svcs, parts in tier:
        what = f"services {svcs[0]} to {svcs[-1]}"
        words.append(f'val {word(gid)} = Param[({L}, BigInt) => Boolean]("{word(gid)}", '
                     f'"whether {what} serve a request to a reader, and show nothing under the reader\'s floor")')
        body = (" &&\n    ".join(ok(i) for i in svcs) if t == 0
                else " &&\n    ".join(f"{word(p)}(xs, f)" for p in parts))
        made_of = "" if t == 0 else f" ({', '.join(parts)})"
        definitions.append(
            f'val {lower(gid)}Terms = Node.definition("{gid}Terms", "{gid} is {what}{made_of}.",\n'
            f'  why = "Services are grouped five by five, so that what a group promises is said once, in one word."\n'
            f')({word(gid)} := ((xs: {L}, f: BigInt) =>\n    {body}))\n')
        floor = ""
        if t == 0:
            floor = (f'\n\n/** The floor, for {what}: kept by each of their contracts. */\n'
                     f'val {lower(floor_id(gid))} = Node.invariant[BigInt, BigInt]("{floor_id(gid)}", '
                     f'"No value {what} show is under the reader\'s floor.",\n'
                     f'  why = "What must never happen, whatever the service: kept by each call, checked on every result.", '
                     f'idea = "Clearance",\n  scope = List({lower(gid)}))((f, x) => visible(x, f)).under({lower(gid)})')
        claims.append(
            f'val {lower(gid)} = Node.claim("{gid}", "{what.capitalize()} serve their requests, each within its bounds, '
            f'and never show a value under the floor.",\n'
            f'  why = "One {"group" if t == 0 else "area"} of the catalog: no claim has more than five parts besides its floor.", idea = "Services")(\n'
            f'  forall((xs: {L}, f: BigInt) => {word(gid)}(xs, f))).under({lower(parent_of[gid])}){floor}\n')

write(os.path.join(src, "Groups.scala"), "package scale\n\nimport frflow.*\n\n"
      "// What each group (and area) of services promises, and the catalog: one word each.\n\n" +
      "\n".join(words) + "\n" +
      f'val catalogOk = Param[({L}, BigInt) => Boolean]("catalogOk", '
      f'"whether every service serves a request to a reader, and shows nothing under the reader\'s floor")\n\n' +
      "\n".join(definitions) +
      f'\nval catalogTerms = Node.definition("CatalogTerms", "The catalog is {", ".join(top)}.",\n'
      f'  why = "The root speaks of the whole catalog in one word."\n'
      f')(catalogOk := ((xs: {L}, f: BigInt) => {" && ".join(f"{word(g)}(xs, f)" for g in top)}))\n')

write(os.path.join(src, "Catalog.scala"), f'''package scale

import frflow.*

// ============================================================================
// The purpose: what a reader can see, and what they never see, together
// ============================================================================

val catalog = Node.claim("Catalog",
  "Every service shows a reader the visible values of each request, within its bounds, and never a value under the reader's floor.",
  why = "The idea: readers get what they may see from every service, and nothing under their clearance, whatever the service."
)(forall((xs: {L}, f: BigInt) => catalogOk(xs, f)))

// ============================================================================
// The areas and groups of services
// ============================================================================

''' + "\n".join(reversed(claims)))

# ---------------------------------------------------------------------------------------------
# The services
# ---------------------------------------------------------------------------------------------
def service_head(i):
    b = bounded(i)
    words = "the visible values of each request within the limit" if b else "the visible values of each request"
    note = f" It reuses service {i - 1}, keeping what is within the limit." if calls(i) else ""
    within = ""
    if b and shared_by(i) is None:
        within = f'''
val withinLimit{i} = Node.claim("WithinLimit{i}", "Service {i} shows no value over the limit.",
  why = "Service {i} is bounded.")(
  forall((xs: {L}, f: BigInt) => serve{i}(xs, f).forall(x => x <= limit.value))).under(service{i})
'''
    if b:
        all_visible = f'''Node.claim("AllVisible{i}", "Service {i} shows every visible value of the request within the limit.",
  why = "A bounded service leaves out only what is over the limit.")(
  forall((xs: {L}, f: BigInt) => xs.forall(x => (visible(x, f) && x <= limit.value) ==> serve{i}(xs, f).contains(x))))'''
    else:
        all_visible = f'''Node.claim("AllVisible{i}", "Service {i} shows every visible value of the request.",
  why = "A reader asking service {i} is not refused what they may see.")(
  forall((xs: {L}, f: BigInt) => xs.forall(x => visible(x, f) ==> serve{i}(xs, f).contains(x))))'''
    return f'''// Service {i} ({"bounded" if b else "open"}).{note}

val service{i} = Node.claim("Service{i}", "Service {i} shows {words}, and nothing from elsewhere.",
  why = "Readers ask service {i} for {'bounded' if b else 'whole'} lists.")(
  forall((xs: {L}, f: BigInt) => {served(i)})).under({lower(group_of[i])})

val fromRequest{i} = Node.claim("FromRequest{i}", "Service {i} shows only values from the request.",
  why = "A service shows what it was asked about, not values from elsewhere.")(
  forall((xs: {L}, f: BigInt) => serve{i}(xs, f).forall(x => xs.contains(x)))).under(service{i})
{within}
val allVisible{i} = {all_visible}.under(service{i})
'''


def service_contract(i):
    b = bounded(i)
    parts = [f"fromRequest{i}"] + ([lower(within_id(i))] if b else []) + [f"allVisible{i}"]
    if b:
        post = ("(xs, f, r) => r.forall(x => xs.contains(x) && visible(x, f) && x <= limit.value) && "
                "xs.forall(x => (visible(x, f) && x <= limit.value) ==> r.contains(x))")
        stmt = "A call shows the request's visible values within the limit, and nothing else."
        examples = '''    expect(List(BigInt(1), BigInt(5), BigInt(2000)), BigInt(3), List(BigInt(5)), "the visible value within the limit"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing visible"),
    reject(List(BigInt(5), BigInt(2000)), BigInt(3), List(BigInt(5), BigInt(2000)), "a value over the limit is never shown"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1), BigInt(5)), "a value under the floor is never shown")'''
        body = f"serve{i - 1}(xs, f).filter(x => x <= limit.value)" if calls(i) else "xs.filter(x => x >= f && x <= limit.value)"
    else:
        post = "(xs, f, r) => r.forall(x => xs.contains(x) && visible(x, f)) && xs.forall(x => visible(x, f) ==> r.contains(x))"
        stmt = "A call shows the request's visible values, and nothing else."
        examples = '''    expect(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "only the visible value"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing visible"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never shown"),
    reject(List(BigInt(5), BigInt(7)), BigInt(3), List(BigInt(5)), "a visible value is not left out")'''
        body = "xs.filter(x => x >= f)"
    return f'''
val show{i} = Node.contract(serve{i})("Show{i}", "{stmt}", why = "Service {i}'s parts, for one call, checked on every result.")(
  {post})
  .under({", ".join(parts)})
  .examples()(
{examples})
  .keeps({lower(floor_id(group_of[i]))})((xs, f, r) => r.map(x => (f, x)))

val shown{i} = define {{ (xs: {L}, f: BigInt) => {body} }}
'''


done = set()
for i in range(n):
    if i in done:
        continue
    if pair_first(i):
        j = i + 2
        w = within_id(i)
        text = (service_head(i) + "\n" + service_head(j) + f'''
/** Shared by services {i} and {j}: the bound is one rule for both, decided once. */
val {lower(w)} = Node.claim("{w}", "Services {i} and {j} show no value over the limit.",
  why = "Both are bounded by the same rule, decided once for the pair.")(
  forall((xs: {L}, f: BigInt) => serve{i}(xs, f).forall(x => x <= limit.value) && serve{j}(xs, f).forall(x => x <= limit.value)))
  .under(service{i}, service{j})
''' + service_contract(i) + service_contract(j))
        write(os.path.join(src, f"Services{i}And{j}.scala"), "package scale\n\nimport frflow.*\n\n" + text)
        done |= {i, j}
    else:
        write(os.path.join(src, f"Service{i}.scala"), "package scale\n\nimport frflow.*\n\n" + service_head(i) + service_contract(i))
        done.add(i)

hand = [i for i in range(n) if i % 10 == 9]
for i in hand:
    write(os.path.join(proofs, f"Service{i}.lean"), f'''import FrFlowGen.Scale.Service{i}.Spec

/-! Authored proofs of the obligations of Service{i}. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Scale.Service{i}.Proofs
open Scale.Service{i}

/-- By hand: serving is showing only the request's values, and every visible one; the parts say each. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro serve{i} h_from h_all
  simp only [frflow_defs] at *
  intro xs f
  exact ⟨h_from xs f, h_all xs f⟩

end Scale.Service{i}.Proofs
''')

# ---------------------------------------------------------------------------------------------
# The knowledge base
# ---------------------------------------------------------------------------------------------
service_nodes = []
for i in range(n):
    service_nodes += [f"service{i}", f"fromRequest{i}"]
    if bounded(i) and shared_by(i) in (None, i):
        service_nodes.append(lower(within_id(i)))
    service_nodes += [f"allVisible{i}", f"show{i}"]
group_nodes = [x for tier in reversed(tiers) for gid, _, _ in tier
               for x in [lower(gid), lower(gid) + "Terms"] + ([lower(floor_id(gid))] if gid.startswith("Group") else [])]
nodes = ["catalog", "catalogTerms", "clearance", "limits", "serving"] + group_nodes + service_nodes
impls = "".join(f"\n  .implementProven(show{i})(shown{i})" for i in range(n))
write(os.path.join(src, "Scale.scala"), f'''package scale

import frflow.*

/** Every node, listed: the root, the vocabulary, the groups, then each service's. */
val knowledge = KnowledgeBase("Scale", idea = "IDEA.md")(
  {(",\n  ").join(nodes)}){impls}

@main def scaleCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/scale"))
''')

write(os.path.join(root, "IDEA.md"), """# Scale

A catalog of services shows readers the values of their requests: each service shows a reader every
value of the request they may see (some services only up to a limit), and no service ever shows a
reader a value under their floor. A synthetic project, to measure FrFlow as it grows.

## Services

Every service serves its requests: only the request's values, and every one the reader may see.
Bounded services leave out what is over the limit.

## Clearance

A reader's floor is their clearance: no value under it is ever shown to them, by any service.
""")

write(os.path.join(root, "lean", "lakefile.toml"), '''name = "scale"
defaultTargets = ["FrFlowGen"]

[[require]]
name = "frflow"
path = "../../../lean"

[[lean_lib]]
name = "FrFlowGen"
globs = ["FrFlowGen.+"]

[[lean_lib]]
name = "Proofs"
globs = ["Proofs.+"]
''')
write(os.path.join(root, "frflow.json"), '''{
  "name": "Scale",
  "run": ["sbt", "--client", "scale/run {args}"],
  "cwd": "../..",
  "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"]
}
''')
for f in ["lean-toolchain", "lake-manifest.json"]:
    t = open(os.path.join(root, "..", "auth", "lean", f)).read()
    write(os.path.join(root, "lean", f), t.replace('"auth"', '"scale"'))

print(f"examples/scale: {len(nodes)} nodes ({n} services, {len(groups)} groups, {sum(len(t) for t in tiers[1:])} areas); "
      f"{len(hand)} splits proven by hand ({', '.join(f'Service{i}' for i in hand) or 'none'})")
