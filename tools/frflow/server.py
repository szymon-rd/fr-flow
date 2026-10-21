#!/usr/bin/env python3
"""FrFlow browser: tracks the process and shows the knowledge base as a tree.

    python3 tools/frflow/server.py examples            # every project under examples/
    python3 tools/frflow/server.py examples/auth --port 8765

The tree comes from `.frflow/kb.json`, which the knowledge base's CLI writes from
the Scala definitions. The Render button (or an agent through the MCP server)
runs the CLI again; open pages update when the snapshot or the event log changes.

API (all JSON):
    GET  /api/projects                     names, and whether a command is running
    GET  /api/p/NAME/kb                    the snapshot, plus `sourcesChanged`
    GET  /api/p/NAME/events?limit=N        the event log
    GET  /api/p/NAME/job                   the last command started here, with its output
    POST /api/p/NAME/run  {"args": [...]}  starts render / check / scaffold / accept
    POST /api/p/NAME/requests {"node", "text", "by"}   asks the agent for something
    POST /api/p/NAME/requests/ID {"status", "answer"}  closes a request
    POST /api/p/NAME/idea {"text"}         saves the idea, then renders
    GET  /api/stream                       server-sent events on every change
"""

from __future__ import annotations

import argparse
import json
import re
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from frflow_tools import Project, find_projects

UI = Path(__file__).resolve().parent / "ui" / "index.html"
UI_COMMANDS = {"render", "check", "scaffold", "accept"}
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def valid_run(args: list[str]) -> str | None:
    """Why a command from the browser is refused, or None."""
    if not args or args[0] not in UI_COMMANDS:
        return f"command must be one of {sorted(UI_COMMANDS)}"
    if args[0] in ("scaffold", "accept") and (len(args) < 2 or not IDENT.match(args[1])):
        return f"{args[0]} NODE ..."
    if args[0] == "check" and len(args) > 1 and (len(args) > 2 or not IDENT.match(args[1])):
        return "check [NODE]"
    if args[0] == "accept":
        opts = dict(zip(args[2::2], args[3::2]))
        if len(args) % 2 != 0 or "--by" not in opts or not opts["--by"].strip() or set(opts) - {"--by", "--note", "--reject"}:
            return "accept NODE --by NAME [--note TEXT] [--reject ID,ID]"
        if not all(IDENT.match(i) for i in opts.get("--reject", "").split(",") if i):
            return "--reject takes node ids"
    if args[0] in ("render",) and len(args) > 1:
        return "render takes no arguments"
    return None


class Job:
    def __init__(self, args: list[str]):
        self.args = args
        self.started = time.time()
        self.finished: float | None = None
        self.exit_code: int | None = None
        self.output = ""

    def json(self) -> dict:
        return {"args": self.args, "started": self.started, "finished": self.finished,
                "exitCode": self.exit_code, "output": self.output, "running": self.finished is None}


class App:
    def __init__(self, projects: list[Project]):
        self.projects = {p.name: p for p in projects}
        self.jobs: dict[str, Job] = {}
        self.lock = threading.Lock()
        self.changed = threading.Condition()
        self.versions = {name: "" for name in self.projects}
        self.tick = 0

    def start(self, name: str, args: list[str]) -> Job:
        project = self.projects[name]
        with self.lock:
            current = self.jobs.get(name)
            if current and current.finished is None:
                raise RuntimeError(f"{' '.join(current.args)} is still running")
            job = Job(args)
            self.jobs[name] = job

        def work() -> None:
            try:
                r = project.run(args, actor="ui")
                job.output, job.exit_code = r.output, r.exit_code
            except Exception as e:  # report, never kill the server
                job.output, job.exit_code = f"{type(e).__name__}: {e}", 1
            job.finished = time.time()
            self.notify()

        threading.Thread(target=work, daemon=True).start()
        self.notify()
        return job

    def notify(self) -> None:
        with self.changed:
            self.tick += 1
            self.changed.notify_all()

    def watch(self, interval: float = 0.5) -> None:
        """Notifies open pages when a snapshot, event log or source changes."""
        while True:
            for name, p in self.projects.items():
                v = p.version()
                if v != self.versions[name]:
                    self.versions[name] = v
                    self.notify()
            time.sleep(interval)


def handler(app: App):
    class Handler(BaseHTTPRequestHandler):
        server_version = "FrFlow"

        def log_message(self, fmt: str, *args) -> None:
            pass

        def send(self, status: int, body: bytes, ctype: str) -> None:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def json(self, value, status: int = 200) -> None:
            self.send(status, json.dumps(value).encode(), "application/json; charset=utf-8")

        def error(self, status: int, message: str) -> None:
            self.json({"error": message}, status)

        def project(self, name: str) -> Project | None:
            p = app.projects.get(name)
            if p is None:
                self.error(HTTPStatus.NOT_FOUND, f"unknown project {name}")
            return p

        def do_GET(self) -> None:
            url = urlparse(self.path)
            parts = [s for s in url.path.split("/") if s]
            query = parse_qs(url.query)
            if url.path in ("/", "/index.html"):
                return self.send(200, UI.read_bytes(), "text/html; charset=utf-8")
            if parts == ["api", "projects"]:
                return self.json([{"name": n, "running": p.running()} for n, p in app.projects.items()])
            if parts == ["api", "stream"]:
                return self.stream()
            if len(parts) == 4 and parts[:2] == ["api", "p"]:
                p = self.project(parts[2])
                if p is None:
                    return
                if parts[3] == "kb":
                    snap = p.snapshot()
                    return self.json({"snapshot": snap, "sourcesChanged": p.sources_changed(), "running": p.running(),
                                      "requests": p.requests()})
                if parts[3] == "events":
                    limit = int(query.get("limit", ["500"])[0])
                    return self.json(p.events(limit))
                if parts[3] == "job":
                    job = app.jobs.get(p.name)
                    return self.json(job.json() if job else None)
            self.error(HTTPStatus.NOT_FOUND, "not found")

        def body(self) -> dict:
            data = json.loads(self.rfile.read(int(self.headers.get("Content-Length", "0"))) or b"{}")
            if not isinstance(data, dict):
                raise ValueError("expected an object")
            return data

        def do_POST(self) -> None:
            # Only this page may change things: refuse requests sent by other sites.
            origin = self.headers.get("Origin")
            if origin and urlparse(origin).netloc != self.headers.get("Host"):
                return self.error(HTTPStatus.FORBIDDEN, "cross-origin request")
            if self.headers.get("Content-Type", "").split(";")[0] != "application/json":
                return self.error(HTTPStatus.UNSUPPORTED_MEDIA_TYPE, "expected application/json")
            parts = [s for s in urlparse(self.path).path.split("/") if s]
            if len(parts) < 4 or parts[:2] != ["api", "p"]:
                return self.error(HTTPStatus.NOT_FOUND, "not found")
            p = self.project(parts[2])
            if p is None:
                return
            try:
                body = self.body()
            except ValueError as e:
                return self.error(HTTPStatus.BAD_REQUEST, f"bad JSON: {e}")
            what = parts[3:]
            if what == ["run"]:
                args = [str(a) for a in body.get("args", [])]
                problem = valid_run(args)
                if problem:
                    return self.error(HTTPStatus.BAD_REQUEST, problem)
                try:
                    return self.json(app.start(p.name, args).json(), HTTPStatus.ACCEPTED)
                except RuntimeError as e:
                    return self.error(HTTPStatus.CONFLICT, str(e))
            if what == ["requests"]:
                node, text, by = str(body.get("node", "")), str(body.get("text", "")).strip(), str(body.get("by", "")).strip()
                if not text or not by or (node and not IDENT.match(node)):
                    return self.error(HTTPStatus.BAD_REQUEST, "expected node, text and by")
                r = p.add_request(node, text, by)
                app.notify()
                return self.json(r, HTTPStatus.CREATED)
            if len(what) == 2 and what[0] == "requests":
                try:
                    r = p.answer_request(what[1], str(body.get("answer", "")), str(body.get("status", "closed")))
                except KeyError as e:
                    return self.error(HTTPStatus.NOT_FOUND, str(e))
                app.notify()
                return self.json(r)
            if what == ["idea"]:
                text = body.get("text")
                if not isinstance(text, str) or not text.strip():
                    return self.error(HTTPStatus.BAD_REQUEST, "expected text")
                p.idea_file.write_text(text if text.endswith("\n") else text + "\n")
                try:
                    return self.json(app.start(p.name, ["render"]).json(), HTTPStatus.ACCEPTED)
                except RuntimeError as e:
                    return self.error(HTTPStatus.CONFLICT, f"saved; {e}")
            self.error(HTTPStatus.NOT_FOUND, "not found")

        def stream(self) -> None:
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            seen = -1
            try:
                while True:
                    with app.changed:
                        app.changed.wait_for(lambda: app.tick != seen, timeout=15)
                        tick = app.tick
                    msg = f"data: {json.dumps({'tick': tick})}\n\n" if tick != seen else ": keep-alive\n\n"
                    seen = tick
                    self.wfile.write(msg.encode())
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError):
                pass

    return Handler


def main() -> None:
    ap = argparse.ArgumentParser(description="FrFlow browser")
    ap.add_argument("projects", nargs="+", help="project directories (with frflow.json), or directories containing them")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8765)
    a = ap.parse_args()
    projects = find_projects(a.projects)
    if not projects:
        raise SystemExit("no project found (a project is a directory with frflow.json)")
    app = App(projects)
    threading.Thread(target=app.watch, daemon=True).start()
    server = ThreadingHTTPServer((a.host, a.port), handler(app))
    server.daemon_threads = True
    print(f"FrFlow browser on http://{a.host}:{server.server_address[1]}  ({', '.join(app.projects)})", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
