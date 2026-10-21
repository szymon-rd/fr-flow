"""Stands in for a knowledge base's CLI in tests: writes a branching snapshot and events."""
import json, os, shlex, sys, time
from pathlib import Path

args = shlex.split(sys.argv[1]) if len(sys.argv) > 1 else []
state = Path(".frflow"); state.mkdir(exist_ok=True)

def node(id, kind, parent, link, verification, **kw):
    n = {"id": id, "kind": kind, "statement": f"{id} statement, long enough to wrap onto a second line of the card.",
         "parent": parent, "sources": {"spec": f"m => spec_{id}(m)"} | ({"abs": "m => m"} if kind == "refine" else {}),
         "substitutions": [{"name": "T", "value": "of[Int]"}] if kind == "instantiate" else [],
         "obligation": None if kind in ("root", "instantiate") else {"statement": f"∀ m, spec m → {parent}.spec (abs m)", "description": f"Every model that meets {id} meets {parent}."},
         "link": link, "proof": None, "rootTheorem": "theorem root : ∀ m, spec m → rootSpec (toRoot m)", "lean": "-- generated",
         "why": f"Because {id} is the right step.", "decision": "proposed", "decided": None,
         "content": {"statement": f"{id} statement", "why": f"Because {id}.", "sources": {"spec": f"m => spec_{id}(m)"}, "substitutions": [], "examples": []},
         "examples": [], "verification": verification, "messages": [], "axioms": ["propext"]}
    n.update(kw)
    return n

def L(status, detail=""): return {"status": status, "detail": detail}

snapshot = {
    "name": "Fake", "idea": "# Fake\n\nAn idea with **bold** and `code`.\n\n- one\n- two\n", "root": "Root",
    "exportedAt": "2026-01-01T00:00:00Z", "roots": ["Root"], "opaques": ["T"], "params": [{"name": "p", "type": "(T → Prop)"}],
    "types": [{"name": "Box", "lean": "structure Box where\n  n : Int"}], "defs": [],
    "nodes": [
        node("Root", "root", None, None, "proven"),
        node("Auto", "refine", "Root", L("proven", "auto"), "proven"),
        node("Inst", "instantiate", "Auto", L("proven", "instantiation"), "proven"),
        node("Contract", "contract", "Inst", L("proven", "authored"), "proven",
             proof={"file": "lean/Proofs/Fake/Contract.lean", "source": "theorem link : Obl.link := by\n  simp"}),
        node("Open", "refine", "Root", L("open", "frflow_auto found no proof"), "open", messages=["prove it in lean/Proofs/Fake/Open.lean"]),
        node("Failed", "refine", "Auto", L("failed", "must state exactly Obl.link"), "failed"),
        node("Stale", "refine", "Root", L("stale"), "stale"),
    ],
}
def decided(note="", rejected=()):
    return {"by": "dev", "at": "2026-01-01T00:00:00Z", "note": note,
            "content": {"statement": "old statement", "why": "old why", "sources": {"spec": "m => old(m)"}, "substitutions": [], "examples": []},
            "rejected": [{"id": r, "statement": f"{r} statement", "why": f"{r} why"} for r in rejected]}

ns = {n["id"]: n for n in snapshot["nodes"]}
ns["Root"].update(decision="accepted", decided=decided("The idea's one rule."))
ns["Auto"].update(decision="accepted", decided=decided("Simplest.", ["Discarded"]))
ns["Inst"].update(decision="proposed")
ns["Contract"].update(decision="changed", decided=decided("first version"))
ns["Failed"].update(decision="parent-changed", decided=decided())
ns["Stale"].update(decision="rejected")
ns["Contract"]["examples"] = [
    {"note": "a good case", "given": ["p.bind(1)"], "call": "(1, 2) ⇒ 3", "expected": True, "contract": "ok", "implementation": "ok"},
    {"note": "a bad case", "given": ["p.bind(1)"], "call": "(1, 2) ⇒ 4", "expected": False, "contract": "ok", "implementation": None},
    {"note": "lazy implementation", "given": ["p.bind(1)"], "call": "(2, 2) ⇒ 4", "expected": True, "contract": "ok", "implementation": "returned 0"},
]
snapshot["nodes"].append(node("Inst2", "instantiate", "Auto", L("proven", "instantiation"), "proven"))

cmd = args[0] if args else ""
if os.environ.get("FAKE_FAIL"):
    print("[error] -- Error: model.scala:3: Not found: foo"); sys.exit(1)
if cmd in ("render", "check", "accept", "scaffold"):
    (state / "kb.json").write_text(json.dumps(snapshot))
    with open(state / "events.jsonl", "a") as f:
        f.write(json.dumps({"at": "2026-01-01T00:00:00Z", "action": cmd, "node": args[1] if len(args) > 1 else "Root",
                            **({"actor": os.environ["FRFLOW_ACTOR"]} if os.environ.get("FRFLOW_ACTOR") else {})}) + "\n")
print("Picked up JAVA_TOOL_OPTIONS: x")
print("[info] welcome to sbt 1.10.7")
print(f"[info] ran {' '.join(args)}")
