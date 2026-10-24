// The AI agent's layer in the web view: the developer's requests and the agent's answers, the nodes with the agent, the
// agent's queue and its open questions. It reads /api/agent/state and registers with the page's FrFlow.extend.
(() => {
  "use strict";
  const F = window.FrFlow;
  const { call, esc, go, when, line, section, note, box, button, text, act, byId } = F;
  let state = null;
  const withAgent = id => !!state?.withAgent.includes(id);
  const on = q => q.node ? go(q.node) : "the idea";
  const ask = (key, node) => act("ask", key, async () => (await call("/api/agent/ask", { node: node || null, text: text(key) })).json,
    q => `Asked [${q.id}]: the agent sees it in its inbox.`);
  const close = (ids, where) => act(where, "", async () => (await call("/api/agent/close", ids)).json,
    rs => `Closed ${rs.map(r => r.id).join(", ")}.`);
  const task = t => { const [k, v] = Object.entries(t)[0];
    return `<div class="row small">${k === "Replace" ? `${go(v.node)} rejected by ${esc(v.by)}: the agent removes it, or proposes what the reason asks for — ${esc(v.reason)}`
      : k === "Revisit" ? `${go(v.node)} to revisit: ${esc(v.reason)}` : `${go(v.node)} rests on ${v.rejectedParents.map(go).join(", ")}, rejected: the agent moves it`}</div>`; };

  F.extend({
    async load() { const r = await call("/api/agent/state"); state = r.json; return r.text; },
    chip: r => withAgent(r.node.id) ? `<span class="chip s-waiting">with the agent</span>` : "",
    waiting: () => {
      if (!state) return [];
      const answers = state.requests.filter(q => q.status === "answered").length;
      return [state.withAgent.length ? `${state.withAgent.length} with the agent` : "", answers ? `${answers} answer(s) to read` : "",
        state.questions.length ? `${state.questions.length} question(s) to answer in chat` : ""];
    },
    // A node the developer asked about is with the agent: its box says so, and the request can be withdrawn.
    decision: d => {
      const r = d.node, v = r.review, id = r.node.id;
      if (!withAgent(id) || (v.state !== "proposed" && v.state !== "review")) return null;
      const open = state.requests.filter(q => q.node === id && q.status === "open");
      return `<div class="box review"><div class="verdict">With the agent</div>
        ${open.map(q => `<div class="why"><div class="label">${esc(q.by)} asked, ${when(q.at)}</div>${esc(q.text)}</div>`).join("")}
        <div class="muted small">It comes back to you when the agent answers or changes ${esc(id)}.</div>
        <div class="actions">${button("Withdraw the request, and decide it now", "agentClose", open.map(q => q.id).join(","), false, true)}</div>${note("close")}</div>`;
    },
    nodeSections: d => {
      const id = d.node.node.id, mine = (state?.requests || []).filter(q => q.node === id && q.status !== "closed");
      return `<h3>Ask for a change</h3>${mine.map(q => `<div class="row small"><b>${esc(q.by)}</b> <span class="muted">${when(q.at)} · ${esc(q.status)}</span><div>${esc(q.text)}</div>
        ${q.answer ? `<div class="why"><span class="muted">agent:</span> ${esc(q.answer)}</div>` : ""}${q.status === "answered" ? `<div class="actions">${button("Done: read", "agentClose", q.id, false, true)}</div>` : ""}</div>`).join("")}
        ${box("ask", "e.g. Add an example: a revoked grant refuses access.")}<div class="actions">${button("Ask for a change", "agentAsk", id, false, true)}
        <span class="muted small">The agent sees it in its inbox; ${esc(id)} is with the agent until it answers or changes it.</span></div>${note("ask")}`;
    },
    inboxTop: () => state?.questions.length ? `<h3>The agent's questions: answer them in chat</h3>${state.questions.map(q =>
      `<div class="row small">[${esc(q.id)}] ${esc(q.text)}<div class="muted">assumed: ${esc(q.assumed)}</div></div>`).join("")}` : "",
    inboxSections: () => {
      if (!state) return "";
      const answers = state.requests.filter(q => q.status === "answered"), open = state.requests.filter(q => q.status === "open");
      return `${section("With the agent: you asked for a change", state.withAgent.map(byId).filter(Boolean).map(line).join(""))}
        <h3>Answers to read</h3>${answers.map(q => `<div class="row small">on ${on(q)}<div>${esc(q.text)}</div>
          <div class="why"><span class="muted">agent:</span> ${esc(q.answer)}</div><div class="actions">${button("Done: read", "agentClose", q.id, false, true)}</div></div>`).join("") || `<div class="muted small">None.</div>`}
        <h3>Waiting for the agent</h3>${open.map(q => `<div class="row small">on ${on(q)} · ${esc(q.by)}<div>${esc(q.text)}</div></div>`).join("") +
          state.forAgent.map(task).join("") || `<div class="muted small">None.</div>`}
        <h3>Ask about the whole idea</h3>${box("idea", "e.g. Users can also see who accessed their records: propose where it belongs.")}
        <div class="actions">${button("Send to the agent", "agentAsk", "", false, true)}</div>${note("ask")}`;
    },
    actions: {
      agentAsk: k => ask(k ? "ask" : "idea", k),
      agentClose: (k, b) => close(k.split(","), b.closest(".box") ? "close" : "ask"),
    },
  });
})();
