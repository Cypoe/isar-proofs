// phi-dialects — projectional views over stage files.
//
// The extension NEVER parses a dialect. Every projection is a
// `python host/dialect.py --file X --as D` subprocess whose JSON
// stdout is rendered. The host toolchain is the one truth — the
// editor is a viewport, not a second implementation.

const vscode = require("vscode");
const cp = require("child_process");
const path = require("path");
const fs = require("fs");
const render = require("./render");

let diagnostics;
let specsProvider;
let relProvider;
let panel;

function repoRoot() {
  const cfg = vscode.workspace.getConfiguration("phi");
  const root = cfg.get("repoRoot");
  if (root) return root;
  const folders = vscode.workspace.workspaceFolders || [];
  for (const f of folders) {
    if (fs.existsSync(path.join(f.uri.fsPath, "host", "dialect.py")))
      return f.uri.fsPath;
  }
  return folders.length ? folders[0].uri.fsPath : "";
}

function bridge(file, dialect, extra, cwd) {
  const py = vscode.workspace.getConfiguration("phi")
    .get("pythonPath", "python");
  const args = [path.join(cwd, "host", "dialect.py")];
  if (file) args.push("--file", file);
  args.push("--as", dialect);
  for (const a of extra || []) args.push(a);
  return new Promise((resolve) => {
    cp.execFile(py, args, { cwd, maxBuffer: 64 << 20 },
      (err, stdout, stderr) => {
        try {
          resolve(JSON.parse(stdout));
        } catch (e) {
          resolve({ dialect, ok: false,
            error: `bridge failed: ${err || e} ${stderr}` });
        }
      });
  });
}

// ---------------------------------------------------------------------------
// projections panel
// ---------------------------------------------------------------------------

function showProjection(doc) {
  const html = render.projection(doc);
  if (!panel) {
    panel = vscode.window.createWebviewPanel(
      "phiProjection", `phi.rel projection`,
      vscode.ViewColumn.Beside,
      { enableScripts: false });
    panel.onDidDispose(() => { panel = undefined; });
  }
  panel.webview.html = html;
  panel.title = `${doc.dialect} — ${path.basename(
    doc._file || "dialects")}`;
}

async function cmdProject() {
  const ed = vscode.window.activeTextEditor;
  if (!ed) return;
  const file = ed.document.uri.fsPath;
  const root = repoRoot();
  const auto = await bridge(file, "auto", [], root);
  if (!auto.ok) {
    return vscode.window.showErrorMessage(auto.error);
  }
  const views = auto.data.views || [auto.dialect];
  const pick = await vscode.window.showQuickPick(views, {
    placeHolder: `${path.basename(file)} — detected ${auto.dialect}`,
  });
  if (!pick) return;
  let extra = [];
  if (pick === "eval") {
    const call = await vscode.window.showInputBox({
      prompt: "rel to run (e.g. add)", value: "add" });
    if (!call) return;
    const argsj = await vscode.window.showInputBox({
      prompt: "args as rel-graph term nodes",
      value: '[{"atom":[8,2]},{"atom":[8,3]}]' });
    if (argsj === undefined) return;
    extra = ["--call", call, "--args", argsj];
  }
  const doc = await bridge(file, pick, extra, root);
  doc._file = file;
  showProjection(doc);
}

async function cmdEval() {
  const ed = vscode.window.activeTextEditor;
  const root = repoRoot();
  const file = ed ? ed.document.uri.fsPath : path.join(
    root, "host", "corpus", "stdlib.phi");
  const call = await vscode.window.showInputBox({
    prompt: `rel to run in ${path.basename(file)}`,
    value: "add" });
  if (!call) return;
  const argsj = await vscode.window.showInputBox({
    prompt: "args as rel-graph term nodes (JSON)",
    value: '[{"atom":[8,2]},{"atom":[8,3]}]' });
  if (argsj === undefined) return;
  const doc = await bridge(file, "eval",
    ["--call", call, "--args", argsj], root);
  doc._file = file;
  showProjection(doc);
}

// ---------------------------------------------------------------------------
// tree views — spec status + open-file rel graph
// ---------------------------------------------------------------------------

class SpecItem extends vscode.TreeItem {
  constructor(s) {
    super(s.name || "?", vscode.TreeItemCollapsibleState.None);
    this.description = `${s.layer}/${s.axis}  ${s.status}`;
    this.tooltip = `${s.in || "?"} -> ${s.out || "?"}\n` +
      `status: ${s.status}\nrefuses: ${s.refuses || "-"}`;
    this.iconPath = new vscode.ThemeIcon(
      s.status === "realized" || s.status === "realized-seed"
        ? "pass" : "circle-outline");
  }
}

class SpecsProvider {
  constructor(root) { this.root = root;
    this._em = new vscode.EventEmitter();
    this.onDidChangeTreeData = this._em.event; }
  refresh() { this._em.fire(); }
  getChildren() {
    const dir = path.join(this.root, "host", "specs");
    if (!fs.existsSync(dir)) return [];
    return fs.readdirSync(dir)
      .filter(f => f.endsWith(".json"))
      .map(f => {
        try {
          return new SpecItem(JSON.parse(
            fs.readFileSync(path.join(dir, f), "utf-8")));
        } catch (e) { return new SpecItem({ name: f, status: "?" }); }
      });
  }
  getTreeItem(x) { return x; }
}

class RelProvider {
  constructor() {
    this.graph = undefined;
    this._em = new vscode.EventEmitter();
    this.onDidChangeTreeData = this._em.event; }
  setGraph(g) { this.graph = g; this._em.fire(); }
  refresh() { this._em.fire(); }
  getChildren() {
    const g = this.graph;
    if (!g || !g.rels) return [];
    return g.rels.map(r => {
      const it = new vscode.TreeItem(
        `${r.name}  ${(r.in || []).length}->${(r.out || []).length}`,
        vscode.TreeItemCollapsibleState.None);
      it.description = `${r.dir}${r.shape ? "  " + r.shape : ""}`;
      it.tooltip = `${r.name} : <in> ${r.dir} <out>` +
        (r.shape ? `  shape ${r.shape}` : "");
      it.iconPath = new vscode.ThemeIcon("symbol-method");
      return it;
    });
  }
  getTreeItem(x) { return x; }
}

async function refreshRelTree(root) {
  const ed = vscode.window.activeTextEditor;
  if (!ed) return;
  const file = ed.document.uri.fsPath;
  const doc = await bridge(file, "auto", [], root);
  if (doc.ok && doc.data.graph) {
    relProvider.setGraph(doc.data.graph);
  } else if (doc.ok && doc.dialect === "rel-graph") {
    relProvider.setGraph(doc.data.graph);
  }
}

// ---------------------------------------------------------------------------
// diagnostics — schema verdicts on save (structure, not text)
// ---------------------------------------------------------------------------

async function lint(doc, root) {
  if (doc.languageId !== "phi" && !doc.uri.fsPath.endsWith(".phi"))
    return;
  const res = await bridge(doc.uri.fsPath, "schema", [], root);
  if (!res.ok || res.data.admissible) {
    diagnostics.set(doc.uri, []);
    return;
  }
  const d = new vscode.Diagnostic(
    new vscode.Range(0, 0, 0, 1),
    `schema refuses: ${res.data.refused}`,
    vscode.DiagnosticSeverity.Error);
  d.source = "rel_schema";
  diagnostics.set(doc.uri, [d]);
}

// ---------------------------------------------------------------------------

function activate(ctx) {
  const root = repoRoot();
  diagnostics = vscode.languages.createDiagnosticCollection("phi");
  ctx.subscriptions.push(diagnostics);

  specsProvider = new SpecsProvider(root);
  relProvider = new RelProvider();
  vscode.window.registerTreeDataProvider("phi.specs", specsProvider);
  vscode.window.registerTreeDataProvider("phi.rels", relProvider);

  ctx.subscriptions.push(
    vscode.commands.registerCommand("phi.project", cmdProject),
    vscode.commands.registerCommand("phi.eval", cmdEval),
    vscode.commands.registerCommand("phi.refresh", () => {
      specsProvider.refresh();
      refreshRelTree(root);
    }));

  const lintCur = d => lint(d, root);
  if (vscode.window.activeTextEditor)
    lintCur(vscode.window.activeTextEditor.document);
  ctx.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(lintCur),
    vscode.workspace.onDidOpenTextDocument(lintCur),
    vscode.window.onDidChangeActiveTextEditor(
      e => { if (e) { lintCur(e.document); refreshRelTree(root); } }));
}

function deactivate() {}
module.exports = { activate, deactivate };
