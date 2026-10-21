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
    POST /api/p/NAME/run  {"args": [...]}  starts render / check / scaffold / approve
    GET  /api/stream                       server-sent events: {"project": NAME} on every change
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from frflow_tools import Project, find_projects

UI = Path(__file__).resolve().parent / "ui" / "index.html"
UI_COMMANDS = {"render", "check", "scaffold", "approve"}


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
                    return self.json({"snapshot": snap, "sourcesChanged": p.sources_changed(), "running": p.running()})
                if parts[3] == "events":
                    limit = int(query.get("limit", ["500"])[0])
                    return self.json(p.events(limit))
                if parts[3] == "job":
                    job = app.jobs.get(p.name)
                    return self.json(job.json() if job else None)
            self.error(HTTPStatus.NOT_FOUND, "not found")

        def do_POST(self) -> None:
            parts = [s for s in urlparse(self.path).path.split("/") if s]
            if len(parts) == 4 and parts[:2] == ["api", "p"] and parts[3] == "run":
                p = self.project(parts[2])
                if p is None:
                    return
                try:
                    body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", "0"))) or b"{}")
                    args = [str(a) for a in body.get("args", [])]
                except (ValueError, AttributeError):
                    return self.error(HTTPStatus.BAD_REQUEST, "expected {\"args\": [...]}")
                if not args or args[0] not in UI_COMMANDS:
                    return self.error(HTTPStatus.BAD_REQUEST, f"command must be one of {sorted(UI_COMMANDS)}")
                if args[0] == "approve" and (len(args) != 4 or args[2] != "--by" or not args[3].strip()):
                    return self.error(HTTPStatus.BAD_REQUEST, "approve NODE --by NAME")
                try:
                    return self.json(app.start(p.name, args).json(), HTTPStatus.ACCEPTED)
                except RuntimeError as e:
                    return self.error(HTTPStatus.CONFLICT, str(e))
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
