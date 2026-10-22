"""Generates examples/scale: a synthetic knowledge base of N concerns, each a root, a refinement and a
contract with proven code, one file per concern, every fifth contract calling the previous concern's.
It measures how FrFlow behaves as a project grows: `sbt "scale/run check"` (cold, then after one
change), `sbt "scale/run status"`.

    python3 bench/generate.py 50      # 150 nodes in 50 files
"""
import os, sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "examples", "scale")
src = os.path.join(root, "src", "main", "scala", "scale")
os.makedirs(src, exist_ok=True)
os.makedirs(os.path.join(root, "lean"), exist_ok=True)
for f in os.listdir(src):
    os.remove(os.path.join(src, f))

L = "List[BigInt]"
for i in range(n):
    calls = i > 0 and i % 5 == 0
    body = f"keepCall{i}(xs, f).filter(x => xs.contains(x))" if calls else "xs.filter(x => x >= f)"
    caller = f"val keepCall{i} = keep{i - 1}.caller(\"keepCall{i}\")\n" if calls else ""
    open(os.path.join(src, f"Concern{i}.scala"), "w").write(f'''package scale

import frflow.*

val root{i} = Node.root[({L}, BigInt) => {L}]("Root{i}", "Kept values are at least the floor.", why = "Concern {i} of the synthetic project.", idea = "Concern {i}")(
  keep => forall((xs: {L}, f: BigInt) => keep(xs, f).forall(x => x >= f)))

val bounded{i} = root{i}.refine[({L}, BigInt) => {L}]("Bounded{i}", "Kept values come from the input and are at least the floor.", why = "Values are only ever taken from the input.")(
  abs = keep => keep,
  spec = keep => forall((xs: {L}, f: BigInt) => keep(xs, f).forall(x => xs.contains(x) && x >= f)))

val keep{i} = bounded{i}.contract[{L}, BigInt, {L}]("Keep{i}", "A call keeps input values at least the floor.", why = "The per-call form of Bounded{i}.")(
  (xs, f, r) => r.forall(x => xs.contains(x) && x >= f))
  .examples()(
    expect(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "only the value over the floor"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing over the floor"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never kept"))

{caller}val kept{i} = define {{ (xs: {L}, f: BigInt) => {body} }}
''')

nodes = ", ".join(f"root{i}, bounded{i}, keep{i}" for i in range(n))
impls = "".join(f"\n  .implementProven(keep{i})(kept{i})" for i in range(n))
open(os.path.join(src, "Scale.scala"), "w").write(f'''package scale

import frflow.*

val knowledge = KnowledgeBase("Scale", idea = "IDEA.md")({nodes}){impls}

@main def scaleCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/scale"))
''')
open(os.path.join(root, "IDEA.md"), "w").write("# Scale\n\nA synthetic project, to measure FrFlow as it grows.\n\n" +
    "".join(f"## Concern {i}\n\nValues kept by concern {i} are at least its floor.\n\n" for i in range(n)))
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
print(f"examples/scale: {3 * n} nodes in {n} files")
