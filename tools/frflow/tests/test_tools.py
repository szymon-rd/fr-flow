"""Tests of the browser backend and the MCP server, against a fake knowledge base CLI.

    python3 -m unittest discover tools/frflow/tests
"""
import json
import os
import shutil
import sys
import tempfile
import threading
import time
import unittest
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import frflow_tools as ft  # noqa: E402
import mcp_server  # noqa: E402
import server  # noqa: E402


class FakeProject(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp()) / "fake"
        shutil.copytree(HERE / "fake", self.dir)
        self.project = ft.Project(self.dir)

    def tearDown(self):
        shutil.rmtree(self.dir.parent, ignore_errors=True)
        os.environ.pop("FAKE_FAIL", None)


class ToolsTest(FakeProject):
    def test_run_writes_snapshot_and_records_the_actor(self):
        r = self.project.run(["render"], actor="agent")
        self.assertTrue(r.ok, r.output)
        self.assertEqual(r.output, "ran render")  # sbt noise removed
        self.assertEqual(self.project.snapshot()["root"], "Root")
        self.assertEqual(self.project.events()[-1]["actor"], "agent")
        self.assertIsNone(self.project.running())

    def test_unknown_commands_are_refused(self):
        with self.assertRaises(ValueError):
            self.project.run(["rm", "-rf"], actor="agent")

    def test_arguments_are_quoted_for_sbt(self):
        self.assertEqual(ft.quote("Node"), "Node")
        self.assertEqual(ft.quote("Ada Lovelace"), '"Ada Lovelace"')
        self.assertEqual(self.project.command(["approve", "Root", "--by", "Ada L"]),
                         ["python3", "fake_cli.py", 'approve Root --by "Ada L"'])

    def test_sources_changed_after_the_snapshot(self):
        self.assertEqual(self.project.sources_changed(), ["(no snapshot yet)"])
        self.project.run(["render"], actor="ui")
        self.assertEqual(self.project.sources_changed(), [])
        later = time.time() + 5
        os.utime(self.dir / "model.txt", (later, later))
        self.assertEqual(self.project.sources_changed(), ["model.txt"])

    def test_tree_text_shows_links(self):
        self.project.run(["render"], actor="ui")
        tree = ft.node_tree(self.project.snapshot())
        self.assertIn("Root (root)  [proven, approved]", tree)
        self.assertIn("  Auto (refine)  [link proven (auto), proven, unapproved]", tree)
        self.assertIn("    Failed (refine)  [link failed (must state exactly Obl.link), failed, unapproved]", tree)


class McpTest(FakeProject):
    def call(self, srv, method, params=None, mid=1):
        return srv.handle({"jsonrpc": "2.0", "id": mid, "method": method, "params": params or {}})

    def test_protocol(self):
        srv = mcp_server.Server([self.project])
        init = self.call(srv, "initialize", {"protocolVersion": "2025-06-18"})["result"]
        self.assertEqual(init["serverInfo"]["name"], "frflow")
        self.assertIsNone(srv.handle({"jsonrpc": "2.0", "method": "notifications/initialized"}))
        names = [t["name"] for t in self.call(srv, "tools/list")["result"]["tools"]]
        self.assertEqual(names, ["render", "check", "status", "context", "scaffold", "tree", "node", "history"])
        self.assertNotIn("approve", names)
        self.assertEqual(self.call(srv, "nope")["error"]["code"], -32601)

    def test_render_then_read_the_tree(self):
        srv = mcp_server.Server([self.project])
        r = self.call(srv, "tools/call", {"name": "tree", "arguments": {}})["result"]
        self.assertTrue(r["isError"])  # no snapshot yet
        r = self.call(srv, "tools/call", {"name": "render", "arguments": {}})["result"]
        self.assertFalse(r["isError"], r)
        self.assertIn("Contract (contract)", r["content"][0]["text"])
        node = json.loads(self.call(srv, "tools/call", {"name": "node", "arguments": {"node": "Open"}})["result"]["content"][0]["text"])
        self.assertEqual(node["link"]["status"], "open")
        self.assertEqual(self.project.events()[-1]["actor"], "agent")

    def test_errors_are_tool_errors(self):
        srv = mcp_server.Server([self.project])
        os.environ["FAKE_FAIL"] = "1"
        r = self.call(srv, "tools/call", {"name": "render", "arguments": {}})["result"]
        self.assertTrue(r["isError"])
        self.assertIn("Not found: foo", r["content"][0]["text"])
        r = self.call(srv, "tools/call", {"name": "context", "arguments": {}})["result"]
        self.assertTrue(r["isError"])

    def test_several_projects_need_a_name(self):
        other = Path(tempfile.mkdtemp()) / "other"
        shutil.copytree(HERE / "fake", other)
        cfg = json.loads((other / "frflow.json").read_text()) | {"name": "Other"}
        (other / "frflow.json").write_text(json.dumps(cfg))
        try:
            srv = mcp_server.Server([self.project, ft.Project(other)])
            r = self.call(srv, "tools/call", {"name": "tree", "arguments": {}})["result"]
            self.assertIn("several projects", r["content"][0]["text"])
        finally:
            shutil.rmtree(other.parent)


class ServerTest(FakeProject):
    def setUp(self):
        super().setUp()
        from http.server import ThreadingHTTPServer
        self.app = server.App([self.project])
        self.httpd = ThreadingHTTPServer(("127.0.0.1", 0), server.handler(self.app))
        self.httpd.daemon_threads = True
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()
        self.base = f"http://127.0.0.1:{self.httpd.server_address[1]}"

    def tearDown(self):
        self.httpd.shutdown()
        self.httpd.server_close()
        super().tearDown()

    def get(self, path):
        with urllib.request.urlopen(self.base + path) as r:
            return r.status, r.read()

    def post(self, path, body):
        req = urllib.request.Request(self.base + path, json.dumps(body).encode(), {"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req) as r:
                return r.status, json.loads(r.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def test_ui_and_api(self):
        status, html = self.get("/")
        self.assertEqual(status, 200)
        self.assertIn(b"FrFlow", html)
        self.assertEqual(json.loads(self.get("/api/projects")[1])[0]["name"], "Fake")
        self.assertIsNone(json.loads(self.get("/api/p/Fake/kb")[1])["snapshot"])

        status, job = self.post("/api/p/Fake/run", {"args": ["render"]})
        self.assertEqual(status, 202)
        for _ in range(100):
            job = json.loads(self.get("/api/p/Fake/job")[1])
            if not job["running"]:
                break
            time.sleep(0.05)
        self.assertEqual(job["exitCode"], 0)
        kb = json.loads(self.get("/api/p/Fake/kb")[1])
        self.assertEqual(len(kb["snapshot"]["nodes"]), 7)
        self.assertEqual(json.loads(self.get("/api/p/Fake/events")[1])[-1]["actor"], "ui")

    def test_commands_are_restricted(self):
        self.assertEqual(self.post("/api/p/Fake/run", {"args": ["status"]})[0], 400)
        self.assertEqual(self.post("/api/p/Fake/run", {"args": ["approve", "Root"]})[0], 400)
        self.assertEqual(self.post("/api/p/Nope/run", {"args": ["render"]})[0], 404)


if __name__ == "__main__":
    unittest.main()
