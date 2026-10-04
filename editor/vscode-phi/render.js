// render.js — dialect-keyed projection HTML.
// Every renderer consumes the bridge's JSON, never source text.

function esc(s) {
  return String(s).replace(/[&<>"]/g,
    c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
}

function page(title, body) {
  return `<!doctype html><meta charset="utf-8"><style>
body { font: 13px/1.5 var(--vscode-editor-font-family, monospace);
       color: var(--vscode-foreground); padding: 1em; }
h1 { font-size: 1.2em; } h2 { font-size: 1em; margin-top: 1.4em; }
.rel, .card { border: 1px solid var(--vscode-panel-border);
  border-radius: 4px; padding: .6em .9em; margin: .6em 0; }
.sig { color: var(--vscode-symbolIcon-methodForeground); }
.shape, .badge { font-size: .8em; padding: 0 .5em; border-radius: 3px;
  background: var(--vscode-badge-background);
  color: var(--vscode-badge-foreground); margin-left: .5em; }
.refused { color: var(--vscode-errorForeground); }
.ok { color: var(--vscode-testing-iconPassed); }
.goal { margin-left: 1.2em; }
tt { background: var(--vscode-textCodeBlock-background);
     padding: 0 .3em; border-radius: 3px; }
table { border-collapse: collapse; }
td, th { border: 1px solid var(--vscode-panel-border);
         padding: .25em .8em; text-align: left; }
details summary { cursor: pointer; }
pre { background: var(--vscode-textCodeBlock-background);
      padding: .8em; overflow-x: auto; }
</style><h1>${esc(title)}</h1>${body}`;
}

// ---------------------------------------------------------------------------
// phi.rel/1 node renderers — mirrors host/phi_rel.py shapes exactly:
// terms: var wild atom atom_dyn pair sym op call_term typed type
//        const var_delta goalterm
// goals: unify cmp call builtin run choice emit fresh
// ---------------------------------------------------------------------------

function aexpr(e) {
  if (!e) return "?";
  if (e.const != null) return String(e.const);
  if (e.var_delta)
    return e.var_delta[0] +
      (e.var_delta[1] ? (e.var_delta[1] > 0 ? "+" : "") +
        e.var_delta[1] : "");
  return JSON.stringify(e);
}

function term(t) {
  if (t == null) return "_";
  if (t.wild) return "_";
  if (t.var != null) return esc(t.var);
  if (t.var_delta) return esc(aexpr(t));
  if (t.const != null) return String(t.const);
  if (t.atom) {
    if (t.atom[0] === 0 && t.atom[1] === 0) return "[]";
    return `ATOM(${t.atom[0]},${t.atom[1]})`;
  }
  if (t.atom_dyn)
    return `ATOM(${esc(aexpr(t.atom_dyn[0]))},` +
      `${esc(aexpr(t.atom_dyn[1]))})`;
  if (t.pair) {
    // right-nested pair chain renders as a list
    const items = [];
    let cur = t;
    while (cur && cur.pair) { items.push(cur.pair[0]); cur = cur.pair[1]; }
    if (cur && cur.atom && cur.atom[0] === 0 && cur.atom[1] === 0)
      return `[${items.map(term).join(", ")}]`;
    return `(${term(t.pair[0])} . ${term(t.pair[1])})`;
  }
  if (t.sym != null) return `'${esc(t.sym)}`;
  if (t.type) return esc(t.type);
  if (t.typed) return `${term(t.typed[0])} : ${esc(t.typed[1])}`;
  if (t.op)
    return `${esc(t.op[0])}(${t.op[1].map(term).join(", ")})`;
  if (t.call_term)
    return `${esc(t.call_term[0])}&lt;` +
      `${t.call_term[1].map(term).join(", ")}&gt;`;
  if (t.goalterm != null) return `<tt>${esc(JSON.stringify(t.goalterm))}</tt>`;
  return `<tt>${esc(JSON.stringify(t))}</tt>`;
}

function goal(g) {
  if (g.unify) return `${term(g.unify[0])} = ${term(g.unify[1])}`;
  if (g.cmp) return `${term(g.cmp[1])} ${esc(g.cmp[0])} ` +
    `${term(g.cmp[2])}`;
  if (g.call)
    return `${esc(g.call.rel)}&lt;${g.call.args.map(term).join(", ")}` +
      `&gt;${g.call.out ? " = " + term(g.call.out) : ""}`;
  if (g.builtin)
    return `${esc(g.builtin.name)}(` +
      `${(g.builtin.args || []).map(term).join(", ")})` +
      `${g.builtin.out ? " = " + term(g.builtin.out) : ""}`;
  if (g.run)
    return `RUN(${term(g.run.goal)}, ${term(g.run.n)}) = ` +
      term(g.run.out);
  if (g.choice)
    return `CHOICE(${term(g.choice.a)} | ${term(g.choice.b)}) = ` +
      term(g.choice.out);
  if (g.emit) return `! ${term(g.emit)}`;
  if (g.fresh)
    return `fresh (${(g.fresh.vars || []).map(esc).join(", ")}) {` +
      `<div class="goal">${(g.fresh.goals || []).map(goal)
        .join("</div><div class=\"goal\">")}</div>}`;
  return `<tt>${esc(JSON.stringify(g))}</tt>`;
}

function rPhiRel(d) {
  const g = d.graph;
  const rels = g.rels.map(r => {
    const clauses = (r.clauses || []).map((c, i) => {
      const head = `clause ${i}` +
        (c.fresh && c.fresh.length ? `  fresh ${c.fresh.join(",")}` : "") +
        (c.guard && c.guard.length ?
          `  when ${c.guard.map(goal).join(" & ")}` : "");
      const body = (c.goals || []).map(x =>
        `<div class="goal">${goal(x)}</div>`).join("");
      return `<details><summary>${head}</summary>${body}</details>`;
    }).join("");
    return `<div class="rel"><div class="sig"><b>${esc(r.name)}</b> : ` +
      `&lt;${r.in.map(term).join(", ")}&gt; ${esc(r.dir)} ` +
      `&lt;${r.out.map(term).join(", ")}&gt;` +
      (r.shape ? `<span class="shape">shape ${r.shape}</span>` : "") +
      `</div>${clauses}</div>`;
  }).join("");
  return `<p><tt>${esc(g.format)}</tt> — ${g.rels.length} rels</p>` +
    rels;
}

function rSchema(d) {
  return d.admissible
    ? `<div class="card"><span class="ok">admissible</span> — ` +
      `${d.rels} rels, all checks green</div>`
    : `<div class="card"><span class="refused">refused</span> — ` +
      `${esc(d.refused)}</div>`;
}

function rBundle(d) {
  const rows = d.sections.map(s =>
    `<tr><td><tt>${esc(s.kind)}</tt></td>` +
    `<td>u${s.type * 8}</td><td>${s.arity}</td>` +
    `<td>${s.rows}</td><td>${s.length}</td></tr>`).join("");
  const real = Object.entries(d.realization || {}).map(([k, v]) =>
    `<tr><td>${esc(k)}</td><td>${esc(String(v))}</td></tr>`).join("");
  return `<p>${d.bytes} bytes</p>` +
    `<h2>sections</h2><table><tr><th>kind</th><th>cell</th>` +
    `<th>arity</th><th>rows</th><th>bytes</th></tr>${rows}</table>` +
    (real ? `<h2>REALIZATION</h2><table>${real}</table>` : "");
}

function rSpec(d) {
  const impl = typeof d.impl === "object" && d.impl
    ? JSON.stringify(d.impl) : d.impl;
  return `<div class="card"><b>${esc(d.name)}</b>` +
    `<span class="badge">${esc(d.layer)}</span>` +
    `<span class="badge">${esc(d.status)}</span><table>` +
    `<tr><td>in</td><td>${esc(d.in)}</td></tr>` +
    `<tr><td>out</td><td>${esc(d.out)}</td></tr>` +
    `<tr><td>axis</td><td>${esc(d.axis)}</td></tr>` +
    `<tr><td>impl</td><td>${esc(impl)}</td></tr>` +
    `<tr><td>refuses</td><td>${esc(d.refuses)}</td></tr>` +
    `</table></div>`;
}

function rEval(d) {
  return `<div class="card">call <b>${esc(d.call)}</b> — ` +
    `${d.n} solution(s)</div>` +
    `<pre>${d.outs.map(esc).join("\n")}</pre>`;
}

function rDialects(d) {
  if (d.projections) // --list: {projections, detect}
    return `<table><tr><th>projection</th><th>detects</th></tr>` +
      d.projections.map(p =>
        `<tr><td><tt>${esc(p)}</tt></td>` +
        `<td>${d.detect.includes(p) ? "auto" : "—"}</td></tr>`)
        .join("") + `</table>`;
  // toolchain inventory: {dialects: {name: {module, record,
  // surface, note}}, selftests: n}
  const rows = Object.entries(d.dialects || {}).map(([name, v]) =>
    `<tr><td><tt>${esc(name)}</tt></td>` +
    `<td><tt>${esc(v && v.module || "")}</tt></td>` +
    `<td>${esc(v && v.record || "")}</td>` +
    `<td>${esc(v && (v.note || v.surface) || "")}</td></tr>`).join("");
  return `<p>${d.selftests} selftests registered</p>` +
    `<table><tr><th>dialect</th><th>module</th><th>record</th>` +
    `<th>note</th></tr>${rows}</table>`;
}

function rFile(d) {
  return `<div class="card">${d.bytes} bytes,` +
    ` ext <tt>${esc(d.ext)}</tt>,` +
    ` detected <tt>${esc(d.dialect)}</tt></div>`;
}

const RENDER = {
  "phi.rel": rPhiRel, "rel-graph": rPhiRel,
  "schema": rSchema, "bundle": rBundle, "spec": rSpec,
  "eval": rEval, "dialects": rDialects, "file": rFile,
};

function projection(doc) {
  if (!doc.ok) return page(`${doc.dialect} — refused`,
    `<div class="card"><span class="refused">` +
    `${esc(doc.error)}</span></div>`);
  const fn = RENDER[doc.dialect] || (d =>
    `<pre>${esc(JSON.stringify(d, null, 1))}</pre>`);
  return page(doc.dialect, fn(doc.data));
}

module.exports = { projection };
