// The AI agent's layer in the web view: the developer's requests and the agent's answers, the nodes with the agent,
// what is the agent's to do and its questions open. It reads /api/agent/state and registers with FrFlow.extend.
// The developer asks and closes here; nothing here decides.
(() => {
  "use strict";
  const F = window.FrFlow;
  const { call, esc } = F;
  let state = null;
  const on = q => q.node ? esc(q.node) : "the idea";
  const task = t => t.type === "Replace" ? `${esc(t.node)} rejected by ${esc(t.by)}: ${esc(t.reason)}` :
    t.type === "Revisit" ? `${esc(t.node)} to revisit: ${esc(t.reason)}` :
    `${esc(t.node)} rests on rejected ${t.rejectedParents.map(esc).join(", ")}`;

  async function ask(node, text, out) {
    const r = await call("POST", "/api/agent/ask", { node, text });
    out.textContent = r.ok ? `Asked [${r.json.id}]: the agent sees it in its inbox.` : (r.json.error || "refused");
    if (r.ok) await F.reload();
  }

  async function close(ids) {
    const r = await call("POST", "/api/agent/close", ids);
    if (r.ok) await F.reload();
  }

  F.extend({
    async panel(container) {
      const r = await call("GET", "/api/agent/state");
      if (!r.ok) return;
      state = r.json;
      const answers = state.requests.filter(q => q.status === "answered");
      const open = state.requests.filter(q => q.status === "open");
      container.innerHTML = '<section class="card" style="margin-top: 8px"><h2>The agent</h2>' +
        (state.questions.length ? "<h2>Its questions: answer them in chat</h2>" + state.questions.map(q =>
          `<p>[${esc(q.id)}] ${esc(q.text)}<br><span class="dim">assumed: ${esc(q.assumed)}</span></p>`).join("") : "") +
        "<h2>Answers to read</h2>" + (answers.map(q => `<p>on ${on(q)}: ${esc(q.text)}<br>agent: ` +
          `${esc(q.answer && q.answer.text)} <button type="button" data-close="${esc(q.id)}">Read</button></p>`)
          .join("") || '<p class="dim">None.</p>') +
        "<h2>Waiting for the agent</h2>" + ([...open.map(q => `<p>on ${on(q)} · ${esc(q.asked.by)}: ${esc(q.text)}</p>`),
          ...state.forAgent.map(t => `<p>${task(t)}</p>`)].join("") || '<p class="dim">None.</p>') +
        '<h2>Ask about the whole idea</h2><textarea id="agent-idea"></textarea><div class="actions">' +
        '<button type="button" id="agent-ask-idea">Send to the agent</button></div><p id="agent-said"></p></section>';
      container.querySelectorAll("[data-close]").forEach(b => b.onclick = () => close([b.dataset.close]));
      document.getElementById("agent-ask-idea").onclick = () =>
        ask(null, document.getElementById("agent-idea").value, document.getElementById("agent-said"));
    },
    nodeActions(node, actions) {
      const b = document.createElement("button");
      b.type = "button";
      b.textContent = state && state.withAgent.includes(node.id) ? "With the agent: ask more…" : "Ask the agent…";
      b.onclick = () => {
        const box = document.getElementById("said");
        box.innerHTML = '<h2>Ask the agent for a change</h2><textarea id="agent-text"></textarea>' +
          '<div class="actions"><button type="button" id="agent-send">Ask</button></div><p id="agent-out"></p>';
        document.getElementById("agent-send").onclick = () => ask(node.id,
          document.getElementById("agent-text").value, document.getElementById("agent-out"));
      };
      actions.appendChild(b);
    },
  });
})();
