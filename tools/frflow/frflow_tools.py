"""Shared by the FrFlow browser backend and the MCP server.

A project is a directory with a `frflow.json`:

    {
      "name": "Auth",
      "run": ["sbt", "auth/run {args}"],      # how to run the knowledge base's CLI
      "cwd": "../..",                         # where to run it, relative to the project
      "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"]
    }

The knowledge base is defined in Scala. Running its CLI (`render`, `check`, ...)
writes `.frflow/kb.json`, the snapshot of the definitions and of the ledger, and
appends to `.frflow/events.jsonl`. These tools never build the tree themselves:
they run the CLI and read what it wrote.
"""

from __future__ import annotations

import fcntl
import json
import os
import re
import shlex
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

# CLI commands, and whether they may be run by an agent. `approve` is the developer's.
COMMANDS = {"render": True, "check": True, "status": True, "context": True, "scaffold": True, "approve": False}

_NOISE = re.compile(
    r"^(Picked up JAVA_TOOL_OPTIONS|\[info\] (welcome to sbt|loading |set current project|running \(fork\)|compiling |done compiling)"
    r"|\[success\] Total time|\[info\] Fetching|\[warn\] .*(deprecat|sbt 2)).*"
)


def clean_output(text: str) -> str:
    """The CLI's output without sbt's noise and prefixes."""
    lines = []
    for line in text.splitlines():
        if _NOISE.match(line):
            continue
        for prefix in ("[info] ", "[error] "):
            if line.startswith(prefix):
                line = line[len(prefix):]
                break
        if not line.startswith("Picked up JAVA_TOOL_OPTIONS"):
            lines.append(line)
    return "\n".join(lines).strip("\n")


def quote(arg: str) -> str:
    """An argument as sbt's input parser reads it."""
    if arg and not re.search(r'[\s"\\]', arg):
        return arg
    return '"' + arg.replace("\\", "\\\\").replace('"', '\\"') + '"'


@dataclass
class RunResult:
    command: list[str]
    exit_code: int
    output: str

    @property
    def ok(self) -> bool:
        return self.exit_code == 0


class Project:
    def __init__(self, root: Path | str):
        self.root = Path(root).resolve()
        cfg_file = self.root / "frflow.json"
        if not cfg_file.is_file():
            raise FileNotFoundError(f"{cfg_file} not found")
        self.config = json.loads(cfg_file.read_text())
        self.name: str = self.config.get("name", self.root.name)
        self.state = self.root / ".frflow"

    # -- files written by the CLI ---------------------------------------------

    @property
    def snapshot_file(self) -> Path:
        return self.state / "kb.json"

    @property
    def events_file(self) -> Path:
        return self.state / "events.jsonl"

    @property
    def running_file(self) -> Path:
        return self.state / "running.json"

    def snapshot(self) -> dict | None:
        try:
            return json.loads(self.snapshot_file.read_text())
        except (FileNotFoundError, json.JSONDecodeError):
            return None

    def events(self, limit: int | None = None) -> list[dict]:
        try:
            lines = self.events_file.read_text().splitlines()
        except FileNotFoundError:
            return []
        out = []
        for line in lines:
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass
        return out[-limit:] if limit else out

    def running(self) -> dict | None:
        try:
            return json.loads(self.running_file.read_text())
        except (FileNotFoundError, json.JSONDecodeError):
            return None

    # -- sources ----------------------------------------------------------------

    def source_files(self) -> list[Path]:
        files = []
        for rel in self.config.get("sources", []):
            p = self.root / rel
            if p.is_file():
                files.append(p)
            elif p.is_dir():
                files.extend(f for f in p.rglob("*") if f.is_file())
        return files

    def sources_changed(self) -> list[str]:
        """Sources modified after the snapshot was written: the tree may be out of date."""
        try:
            at = self.snapshot_file.stat().st_mtime
        except FileNotFoundError:
            return ["(no snapshot yet)"]
        return sorted(str(f.relative_to(self.root)) for f in self.source_files() if f.stat().st_mtime > at)

    def version(self) -> str:
        """Changes whenever anything the browser shows changes."""
        parts = []
        for f in [self.snapshot_file, self.events_file, self.running_file, *self.source_files()]:
            try:
                st = f.stat()
                parts.append(f"{f}:{st.st_mtime_ns}:{st.st_size}")
            except FileNotFoundError:
                parts.append(f"{f}:-")
        return str(hash("|".join(parts)))

    # -- running the CLI ------------------------------------------------------

    def command(self, args: list[str]) -> list[str]:
        joined = " ".join(quote(a) for a in args)
        return [part.replace("{args}", joined) for part in self.config["run"]]

    def run(self, args: list[str], actor: str, timeout: float = 3600) -> RunResult:
        """Runs the CLI. One command at a time per project, across processes."""
        if not args or args[0] not in COMMANDS:
            raise ValueError(f"unknown command {args[:1]}")
        cmd = self.command(args)
        cwd = (self.root / self.config.get("cwd", ".")).resolve()
        env = dict(os.environ, FRFLOW_ACTOR=actor)
        self.state.mkdir(parents=True, exist_ok=True)
        with open(self.state / "run.lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            self.running_file.write_text(json.dumps({"args": args, "actor": actor, "since": time.time()}))
            try:
                proc = subprocess.run(cmd, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, text=True, timeout=timeout)
                result = RunResult(cmd, proc.returncode, clean_output(proc.stdout))
            except subprocess.TimeoutExpired as e:
                result = RunResult(cmd, 124, clean_output((e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")) + f"\ntimed out after {timeout}s")
            except FileNotFoundError as e:
                result = RunResult(cmd, 127, f"cannot run {shlex.join(cmd)}: {e}")
            finally:
                self.running_file.unlink(missing_ok=True)
        return result


def node_tree(snapshot: dict) -> str:
    """A compact text tree of a snapshot: kind, link to parent, verification, approval."""
    nodes = snapshot.get("nodes", [])
    children: dict[str | None, list[dict]] = {}
    for n in nodes:
        children.setdefault(n.get("parent"), []).append(n)
    lines: list[str] = []

    def go(n: dict, depth: int) -> None:
        link = n.get("link")
        edge = "" if link is None else f"link {link['status']}{' (' + link['detail'] + ')' if link.get('detail') else ''}, "
        lines.append(f"{'  ' * depth}{n['id']} ({n['kind']})  [{edge}{n['verification']}, {n['approval']}]")
        for c in children.get(n["id"], []):
            go(c, depth + 1)

    for r in children.get(None, []):
        go(r, 0)
    return "\n".join(lines)


def find_projects(paths: list[str]) -> list[Project]:
    """Projects at the given paths; a directory without `frflow.json` is searched one level down."""
    out: list[Project] = []
    for p in paths:
        d = Path(p)
        if (d / "frflow.json").is_file():
            out.append(Project(d))
        elif d.is_dir():
            out.extend(Project(c) for c in sorted(d.iterdir()) if (c / "frflow.json").is_file())
    names = [p.name for p in out]
    dup = {n for n in names if names.count(n) > 1}
    if dup:
        raise ValueError(f"duplicate project names: {', '.join(sorted(dup))}")
    return out
