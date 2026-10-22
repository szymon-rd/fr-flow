"""Generates examples/scale: a synthetic knowledge base of N concerns, to measure how FrFlow behaves as a
project grows. Each concern, in a file of its own:

  root (what a user can do: the values kept are exactly those at least the floor)
  → refinement (pointwise: from the input, at least the floor, none left out)
  → refinement (the input's order kept: the filter itself)
  → contract (one call), keeping the invariant every contract keeps, with proven code;
  every fifth contract's code calls the previous concern's, and every tenth concern's second
  refinement is proven by hand (lean/Proofs).

    python3 bench/generate.py 100      # 401 nodes in 100 files
    sbt "scale/run check"             # cold, then after one change; sbt "scale/run status"
"""
import os, sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "examples", "scale")
src = os.path.join(root, "src", "main", "scala", "scale")
proofs = os.path.join(root, "lean", "Proofs", "Scale")
for d in (src, proofs):
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))

L = "List[BigInt]"
open(os.path.join(src, "Invariant.scala"), "w").write(f'''package scale

import frflow.*

/** Stated once, kept by every contract: no value shown is under its floor. */
val atLeastFloor = Node.invariant[BigInt, BigInt]("AtLeastFloor", "No value a call returns is under the call's floor.",
  why = "The rule every concern of the synthetic project keeps.")((f, x) => x >= f)
''')
for i in range(n):
    calls = i > 0 and i % 5 == 0
    body = f"keepCall{i}(xs, f)" if calls else "xs.filter(x => x >= f)"
    caller = f"val keepCall{i} = keep{i - 1}.caller(\"keepCall{i}\")\n" if calls else ""
    open(os.path.join(src, f"Concern{i}.scala"), "w").write(f'''package scale

import frflow.*

val root{i} = Node.root[({L}, BigInt) => {L}]("Root{i}", "The values kept are exactly the input's values at least the floor.",
  why = "Concern {i} of the synthetic project.", idea = "Concern {i}")(
  keep => forall((xs: {L}, f: BigInt) => forall((x: BigInt) => keep(xs, f).contains(x) == (xs.contains(x) && x >= f))))

val bounded{i} = root{i}.refine[({L}, BigInt) => {L}]("Bounded{i}", "Every value kept is from the input and at least the floor, and none is left out.",
  why = "The root, value by value.")(
  abs = keep => keep,
  spec = keep => forall((xs: {L}, f: BigInt) => keep(xs, f).forall(x => xs.contains(x) && x >= f) && xs.forall(x => (x >= f) ==> keep(xs, f).contains(x))))

val ordered{i} = bounded{i}.refine[({L}, BigInt) => {L}]("Ordered{i}", "What is kept is the input's values at least the floor, in the input's order.",
  why = "Callers rely on the order.")(
  abs = keep => keep,
  spec = keep => forall((xs: {L}, f: BigInt) => keep(xs, f) == xs.filter(x => x >= f)))

val keep{i} = ordered{i}.contract[{L}, BigInt, {L}]("Keep{i}", "A call keeps the input's values at least the floor, in order.", why = "Ordered{i}, for one call.")(
  (xs, f, r) => r == xs.filter(x => x >= f))
  .examples()(
    expect(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "only the value over the floor"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing over the floor"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never kept"))
  .keeps(atLeastFloor)((xs, f, r) => r.map(x => (f, x)))

{caller}val kept{i} = define {{ (xs: {L}, f: BigInt) => {body} }}

/** Concern {i}, as the knowledge base takes it: its nodes, and its code attached. */
val concern{i}: (List[Node[?]], KnowledgeBase => KnowledgeBase) = (List(root{i}, bounded{i}, ordered{i}, keep{i}), _.implementProven(keep{i})(kept{i}))
''')
    if i % 10 == 9:
        open(os.path.join(proofs, f"Ordered{i}.lean"), "w").write(f'''import FrFlowGen.Scale.Ordered{i}.Spec

set_option autoImplicit false
noncomputable section
open Classical

namespace Scale.Ordered{i}.Proofs
open Scale.Ordered{i}

/-- By hand: the filter keeps exactly the values at least the floor. -/
theorem link : Obl.link := by
  unfold Obl.link
  intro m h
  simp only [frflow_defs] at *
  intro xs f
  rw [h xs f]
  constructor
  · intro x hx
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hx
  · intro x hx hf
    simp [List.mem_filter, hx, hf]

/-- The root says something here: keeping a value under the floor fails it. -/
theorem nontrivial : Obl.nontrivial := by
  unfold Obl.nontrivial
  refine ⟨fun _ _ => [0], ?_⟩
  simp only [frflow_defs]
  intro h
  have := h [] 0 0
  simp at this

end Scale.Ordered{i}.Proofs
''')

concerns = ", ".join(f"concern{i}" for i in range(n))
open(os.path.join(src, "Scale.scala"), "w").write(f'''package scale

import frflow.*

/** The concerns, each its own file: a large project lists modules, not every node. */
val concerns = List({concerns})

val knowledge = concerns.foldLeft(KnowledgeBase("Scale", idea = "IDEA.md")((atLeastFloor :: concerns.flatMap(_._1))*))((kb, c) => c._2(kb))

@main def scaleCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/scale"))
''')
open(os.path.join(root, "IDEA.md"), "w").write("# Scale\n\nA synthetic project, to measure FrFlow as it grows.\n\n" +
    "".join(f"## Concern {i}\n\nA user can keep the values of a list that are at least a floor, in order.\n\n" for i in range(n)))
open(os.path.join(root, "lean", "lakefile.toml"), "w").write('''name = "scale"
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
open(os.path.join(root, "frflow.json"), "w").write('''{
  "name": "Scale",
  "run": ["sbt", "--client", "scale/run {args}"],
  "cwd": "../..",
  "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"]
}
''')
for f in ["lean-toolchain", "lake-manifest.json"]:
    t = open(os.path.join(root, "..", "crm", "lean", f)).read()
    open(os.path.join(root, "lean", f), "w").write(t.replace('"crm"', '"scale"'))
print(f"examples/scale: {4 * n + 1} nodes in {n} files, {n // 10} links proven by hand")
