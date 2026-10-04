// phi-dialects — projectional views over stage files.
//
// The .plex bundle is the document of record.  The extension never
// parses a dialect: every projection is a `python host/dialect.py`
// subprocess whose JSON stdout is rendered, and every write is a
// `--set` verb that goes parse -> schema -> bundle atomically.
// Editing a .plex means editing one of its projected surfaces —
// the phi-bundle: filesystem below makes that a real document with
// dirty tracking and save-to-rebundle semantics.

const vscode = require("vscode");
const cp = require("child_process");
const path = require("path");
const fs = require("fs");
const render = require("./render");

const FS_SCHEME = "phi-bundle";

let diagnostics;
let specsProvider;
let relProvider;
let panel;
let viewStatus;
const currentView = new Map();   // file path -> dialect view

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

// bridge: spawn so we can pipe stdin for --set
function bridge(file, dialect, extra, cwd, stdin) {
  const py = vscode.workspace.getConfiguration("phi")
    .get("pythonPath", "python");
  const args = [path.join(cwd, "host", "dialect.py")];
  if (file) args.push("--file", file);
  args.push("--as", dialect);
  for (const a of extra || []) args.push(a);
  return new Promise((resolve) => {
    const p = cp.spawn(py, args, { cwd });
    let out = "", err = "";
    p.stdout.on("data", d => out += d);
    p.stderr.on("data", d => err += d);
    p.on("error", e => resolve({ dialect, ok: false,
      error: `bridge spawn failed: ${e}` }));
    p.on("close", () => {
      try { resolve(JSON.parse(out)); }
      catch (e) { resolve({ dialect, ok: false,
        error: `bridge output: ${err || out || e}` }); }
    });
    if (stdin != null) { p.stdin.write(stdin); }
    p.stdin.end();
  });
}

function bridgeSet(file, dialect, cwd, stdin) {
  const py = vscode.workspace.getConfiguration("phi")
    .get("pythonPath", "python");
  const args = [path.join(cwd, "host", "dialect.py"),
    "--file", file, "--set", dialect];
  return new Promise((resolve) => {
    const p = cp.spawn(py, args, { cwd });
    let out = "", err = "";
    p.stdout.on("data", d => out += d);
    p.stderr.on("data", d => err += d);
    p.on("error", e => resolve({ dialect, ok: false,
      error: `bridge spawn failed: ${e}` }));
    p.on("close", () => {
      try { resolve(JSON.parse(out)); }
      catch (e) { resolve({ dialect, ok: false,
        error: `bridge output: ${err || out || e}` }); }
    });
    p.stdin.write(stdin || "");
    p.stdin.end();
  });
}

// ---------------------------------------------------------------------------
// phi-bundle: filesystem — a .plex rel-bundle AS a surface document.
// readFile  = dialect --as phi.rel  -> data.surface
// writeFile = dialect --set phi.rel <- stdin surface (atomic rebundle)
// URI form: phi-bundle:///<abs path to .plex>  (authority empty)
// ---------------------------------------------------------------------------

class PhiBundleFs {
  constructor(root) {
    this.root = root;
    this._em = new vscode.EventEmitter();
    this.onDidChangeFile = this._em.event;
  }
  watch() { return new vscode.Disposable(() => {}); }
  _file(uri) {
    // uri.path carries the absolute path (posix-style, leading /)
    let p = decodeURIComponent(uri.path);
    if (/^\/[A-Za-z]:/.test(p)) p = p.slice(1);   // /C:/x -> C:/x
    return p;
  }
  async readFile(uri) {
    const doc = await bridge(this._file(uri), "phi.rel", [],
      this.root);
    if (!doc.ok) throw vscode.FileSystemError.Unavailable(
      doc.error);
    return Buffer.from(doc.data.surface, "utf-8");
  }
  async writeFile(uri, content, _opts) {
    const res = await bridgeSet(this._file(uri), "phi.rel",
      this.root, Buffer.from(content).toString("utf-8"));
    if (!res.ok) throw vscode.FileSystemError.Unavailable(
      res.error);
  }
  stat(uri) {
    return { type: vscode.FileType.File, ctime: 0,
      mtime: Date.now(), size: 0 };
  }
  readDirectory() { return []; }
  createDirectory() {}
  delete() {}
  rename() {}
}

function bundleUri(plexPath) {
  const p = plexPath.replace(/\\/g, "/");
  return vscode.Uri.parse(
    `${FS_SCHEME}://${p.startsWith("/") ? "" : "/"}${p}`);
}

// ---------------------------------------------------------------------------
// view dropdown — sticky per document, status bar chip
// ---------------------------------------------------------------------------

async function detectViews(file, root) {
  const doc = await bridge(file, "auto", [], root);
  if (!doc.ok) return null;
  return { dialect: doc.dialect,
    views: doc.data.views || [doc.dialect],
    writable: doc.data.writable || [] };
}

function updateStatus(file, views) {
  if (!file) { viewStatus.hide(); return; }
  const cur = currentView.get(file);
  viewStatus.text = `$(symbol-structure) view: ${cur ||
    (views ? views.dialect : "?")}`;
  viewStatus.tooltip = "phi.rel — switch dialect view";
  viewStatus.show();
}

async function showView(file, view, root, views) {
  if (view === "phi.rel" && file.endsWith(".plex")) {
    // the surface view of the canonical bundle: a real editable
    // document over phi-bundle:
    const doc = await vscode.workspace.openTextDocument(
      bundleUri(file));
    await vscode.languages.setTextDocumentLanguage(doc, "phi");
    await vscode.window.showTextDocument(doc,
      { viewColumn: vscode.ViewColumn.Beside, preview: false });
    return;
  }
  let extra = [];
  if (view === "eval") {
    const call = await vscode.window.showInputBox({
      prompt: "rel to run", value: "add" });
    if (!call) return;
    const argsj = await vscode.window.showInputBox({
      prompt: "args as rel-graph term nodes",
      value: '[{"atom":[8,2]},{"atom":[8,3]}]' });
    if (argsj === undefined) return;
    extra = ["--call", call, "--args", argsj];
  }
  const doc = await bridge(file, view, extra, root);
  doc._file = file;
  const html = render.projection(doc);
  if (!panel) {
    panel = vscode.window.createWebviewPanel(
      "phiProjection", `phi.rel projection`,
      vscode.ViewColumn.Beside, { enableScripts: false });
    panel.onDidDispose(() => { panel = undefined; });
  }
  panel.webview.html = html;
  panel.title = `${view} — ${path.basename(file)}`;
}

async function cmdSwitchView() {
  const ed = vscode.window.activeTextEditor;
  if (!ed) return;
  const root = repoRoot();
  let file = ed.document.uri.fsPath;
  if (ed.document.uri.scheme === FS_SCHEME)
    file = ed.document.uri.path.replace(/^\//, "");
  const views = await detectViews(file, root);
  if (!views) {
    return vscode.window.showErrorMessage(
      `no dialect view for ${path.basename(file)}`);
  }
  const pick = await vscode.window.showQuickPick(views.views, {
    placeHolder: `${path.basename(file)} — ${views.dialect}` +
      (views.writable.length ?
        ` (writable: ${views.writable.join(",")})` : ""),
  });
  if (!pick) return;
  currentView.set(file, pick);
  updateStatus(file, views);
  await showView(file, pick, root, views);
}

async function refreshCurrentView(root) {
  const ed = vscode.window.activeTextEditor;
  if (!ed) return;
  const file = ed.document.uri.fsPath;
  const view = currentView.get(file);
  const views = await detectViews(file, root);
  updateStatus(file, views);
  if (view && views && views.views.includes(view))
    await showView(file, view, root, views);
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
  let file = ed.document.uri.fsPath;
  if (ed.document.uri.scheme === FS_SCHEME) {
    // inside a surface view of a bundle — graph comes from the
    // backing .plex
    file = file.endsWith(".plex") ? file : file;
  }
  const doc = await bridge(file, "auto", [], root);
  if (doc.ok && doc.data.graph) {
    relProvider.setGraph(doc.data.graph);
  } else if (doc.ok && doc.dialect === "rel-graph") {
    relProvider.setGraph(doc.data.graph);
  } else if (ed.document.uri.scheme === FS_SCHEME) {
    const g = await bridge(file, "rel-graph", [], root);
    if (g.ok) relProvider.setGraph(g.data.graph);
  }
}

// ---------------------------------------------------------------------------
// diagnostics + canonical write-back
// ---------------------------------------------------------------------------

async function lint(doc, root) {
  let file = doc.uri.fsPath;
  let bundle = null;
  if (doc.uri.scheme === FS_SCHEME) {
    bundle = file;                       // the .plex itself
  } else if (!(doc.languageId === "phi" ||
               file.endsWith(".phi"))) {
    return;
  }
  const res = await bridge(file, "schema", [], root);
  if (!res.ok || res.data.admissible) {
    diagnostics.set(doc.uri, []);
    return;
  }
  const d = new vscode.Diagnostic(
    new vscode.Range(0, 0, 0, 1),
    `schema refuses: ${res.data.refused || res.error}`,
    vscode.DiagnosticSeverity.Error);
  d.source = "rel_schema";
  diagnostics.set(doc.uri, [d]);
}

// .phi save -> write the canonical sibling .rel.plex through --set
async function rebundleOnSave(doc, root) {
  if (doc.uri.scheme !== "file" || !doc.uri.fsPath.endsWith(".phi"))
    return;
  const plex = doc.uri.fsPath.replace(/\.phi$/, ".rel.plex");
  const res = await bridgeSet(plex, "phi.rel", root,
    doc.getText());
  if (res.ok) {
    vscode.window.setStatusBarMessage(
      `$(archive) ${path.basename(plex)} — ${res.data.rels} rels, ` +
      `${res.data.bytes}B`, 4000);
  } else {
    vscode.window.showErrorMessage(
      `rebundle refused: ${res.error}`);
  }
}

// ---------------------------------------------------------------------------

function activate(ctx) {
  const root = repoRoot();
  diagnostics = vscode.languages.createDiagnosticCollection("phi");
  ctx.subscriptions.push(diagnostics);

  ctx.subscriptions.push(
    vscode.workspace.registerFileSystemProvider(
      FS_SCHEME, new PhiBundleFs(root),
      { isCaseSensitive: true }));

  specsProvider = new SpecsProvider(root);
  relProvider = new RelProvider();
  vscode.window.registerTreeDataProvider("phi.specs", specsProvider);
  vscode.window.registerTreeDataProvider("phi.rels", relProvider);

  viewStatus = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right, 50);
  viewStatus.command = "phi.switchView";
  ctx.subscriptions.push(viewStatus);

  ctx.subscriptions.push(
    vscode.commands.registerCommand("phi.switchView", cmdSwitchView),
    vscode.commands.registerCommand("phi.project", cmdSwitchView),
    vscode.commands.registerCommand("phi.eval", async () => {
      const ed = vscode.window.activeTextEditor;
      const root2 = repoRoot();
      const file = ed ? ed.document.uri.fsPath : path.join(
        root2, "host", "corpus", "stdlib.phi");
      currentView.set(file, "eval");
      await showView(file, "eval", root2,
        await detectViews(file, root2));
    }),
    vscode.commands.registerCommand("phi.openSurface", async () => {
      const ed = vscode.window.activeTextEditor;
      if (!ed) return;
      await showView(ed.document.uri.fsPath, "phi.rel",
        repoRoot(), null);
    }),
    vscode.commands.registerCommand("phi.refresh", () => {
      specsProvider.refresh();
      const root2 = repoRoot();
      refreshRelTree(root2);
      refreshCurrentView(root2);
    }));

  const lintCur = d => lint(d, root);
  if (vscode.window.activeTextEditor) {
    lintCur(vscode.window.activeTextEditor.document);
    updateStatus(vscode.window.activeTextEditor.document.uri
      .fsPath, null);
  }
  ctx.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(d => {
      lintCur(d);
      rebundleOnSave(d, root);
    }),
    vscode.workspace.onDidOpenTextDocument(lintCur),
    vscode.window.onDidChangeActiveTextEditor(async e => {
      if (e) {
        lintCur(e.document);
        const root2 = repoRoot();
        refreshRelTree(root2);
        updateStatus(e.document.uri.fsPath,
          await detectViews(e.document.uri.fsPath, root2));
      } else {
        updateStatus(null, null);
      }
    }));
}

function deactivate() {}
module.exports = { activate, deactivate };
