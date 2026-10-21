#!/usr/bin/env python3
"""FrFlow MCP server (stdio): lets an agent work on a knowledge base.

    python3 tools/frflow/mcp_server.py examples

Tools run the knowledge base's CLI, which builds everything from the Scala
definitions: `render` regenerates the Lean and the snapshot `.frflow/kb.json`,
which the FrFlow browser shows. Approving a node is the developer's decision, so
there is no tool for it.
"""

from __future__ import annotations

import json
import sys
import traceback

from frflow_tools import Project, find_projects, node_tree

PROTOCOL_VERSION = "2025-06-18"

_project = {"type": "string", "description": "Project name (optional when there is one project)."}
_node = {"type": "string", "description": "Node id, as in the tree."}


def _schema(props: dict, required: list[str] = ()) -> dict:
    return {"type": "object", "properties": props, "required": list(required), "additionalProperties": False}


TOOLS = [
    {
        "name": "render",
        "description": "Rebuild the knowledge base from the Scala definitions: regenerate the Lean and the snapshot "
                       "shown in the FrFlow browser. Run it after changing a node, the domain or IDEA.md. "
                       "Returns the tree. Compile errors in the Scala model are returned as the error.",
        "inputSchema": _schema({"project": _project}),
    },
    {
        "name": "check",
        "description": "Render, then prove each node's link to its parent in Lean (frflow_auto, or the authored "
                       "proof in lean/Proofs), audit axioms and record the results. Slow (minutes). "
                       "Optionally only one node.",
        "inputSchema": _schema({"project": _project, "node": _node}),
    },
    {
        "name": "status",
        "description": "The tree with each node's approval and verification state, computed from the current definitions.",
        "inputSchema": _schema({"project": _project}),
    },
    {
        "name": "context",
        "description": "Everything needed to work on a node: the idea, the path from the root with Scala sources, "
                       "the obligation in Lean and its state, and the rules. Read it before changing a node.",
        "inputSchema": _schema({"project": _project, "node": _node}, ["node"]),
    },
    {
        "name": "scaffold",
        "description": "Create lean/Proofs/<KB>/<NODE>.lean with a stub for an obligation automation did not prove. "
                       "The proof must state exactly `Obl.link`; axiom, sorry and similar are rejected.",
        "inputSchema": _schema({"project": _project, "node": _node}, ["node"]),
    },
    {
        "name": "tree",
        "description": "The tree from the last snapshot, without running anything (fast). Says if sources changed since.",
        "inputSchema": _schema({"project": _project}),
    },
    {
        "name": "node",
        "description": "One node from the last snapshot as JSON: statement, sources, substitutions, obligation, "
                       "link status, root theorem, generated Lean, approval, axioms.",
        "inputSchema": _schema({"project": _project, "node": _node}, ["node"]),
    },
    {
        "name": "history",
        "description": "The latest events of the process (render, check, approve, scaffold), with who triggered them.",
        "inputSchema": _schema({"project": _project, "limit": {"type": "integer", "minimum": 1, "maximum": 500}}),
    },
]


class ToolError(Exception):
    pass


class Server:
    def __init__(self, projects: list[Project]):
        self.projects = {p.name: p for p in projects}

    def project(self, args: dict) -> Project:
        name = args.get("project")
        if name is None:
            if len(self.projects) == 1:
                return next(iter(self.projects.values()))
            raise ToolError(f"several projects; pass project, one of: {', '.join(self.projects)}")
        if name not in self.projects:
            raise ToolError(f"unknown project {name}; one of: {', '.join(self.projects)}")
        return self.projects[name]

    def run(self, p: Project, args: list[str]) -> tuple[str, bool]:
        r = p.run(args, actor="agent")
        return r.output or f"(exit code {r.exit_code})", not r.ok

    def staleness(self, p: Project) -> str:
        changed = p.sources_changed()
        return f"\n\nSources changed since this snapshot ({', '.join(changed[:5])}); call render." if changed else ""

    def call(self, name: str, args: dict) -> tuple[str, bool]:
        p = self.project(args)
        node = args.get("node")
        if name == "render":
            out, err = self.run(p, ["render"])
            if err:
                return out, True
            snap = p.snapshot()
            return out + ("\n\n" + node_tree(snap) if snap else ""), False
        if name == "check":
            return self.run(p, ["check"] + ([node] if node else []))
        if name == "status":
            return self.run(p, ["status"])
        if name in ("context", "scaffold"):
            if not node:
                raise ToolError("node is required")
            return self.run(p, [name, node])
        snap = p.snapshot()
        if name == "history":
            return "\n".join(json.dumps(e) for e in p.events(int(args.get("limit", 30)))) or "(no events yet)", False
        if snap is None:
            raise ToolError("no snapshot yet; call render")
        if name == "tree":
            return f"{snap['name']}\n\n{node_tree(snap)}{self.staleness(p)}", False
        if name == "node":
            found = next((n for n in snap["nodes"] if n["id"] == node), None)
            if found is None:
                raise ToolError(f"unknown node {node}; nodes: {', '.join(n['id'] for n in snap['nodes'])}")
            return json.dumps(found, indent=2) + self.staleness(p), False
        raise ToolError(f"unknown tool {name}")

    def handle(self, msg: dict) -> dict | None:
        method, mid, params = msg.get("method"), msg.get("id"), msg.get("params") or {}

        def result(value: dict) -> dict:
            return {"jsonrpc": "2.0", "id": mid, "result": value}

        if method == "initialize":
            return result({
                "protocolVersion": params.get("protocolVersion", PROTOCOL_VERSION),
                "capabilities": {"tools": {"listChanged": False}},
                "serverInfo": {"name": "frflow", "version": "0.1.0"},
                "instructions": "FrFlow knowledge bases: " + ", ".join(self.projects) +
                                ". The Scala definitions are the model; these tools render and check them.",
            })
        if method == "ping":
            return result({})
        if method == "tools/list":
            return result({"tools": TOOLS})
        if method == "tools/call":
            try:
                text, is_error = self.call(params.get("name", ""), params.get("arguments") or {})
            except ToolError as e:
                text, is_error = str(e), True
            except Exception as e:
                text, is_error = f"{type(e).__name__}: {e}\n{traceback.format_exc()}", True
            return result({"content": [{"type": "text", "text": text}], "isError": is_error})
        if mid is None:  # a notification
            return None
        return {"jsonrpc": "2.0", "id": mid, "error": {"code": -32601, "message": f"method not found: {method}"}}


def main() -> None:
    projects = find_projects(sys.argv[1:] or ["."])
    if not projects:
        raise SystemExit("no project found (a project is a directory with frflow.json)")
    server = Server(projects)
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            out = {"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "parse error"}}
        else:
            out = server.handle(msg)
        if out is not None:
            sys.stdout.write(json.dumps(out) + "\n")
            sys.stdout.flush()


if __name__ == "__main__":
    main()
