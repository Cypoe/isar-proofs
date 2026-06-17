import { SYSTEMS, edges, familyColors, QUOTIENT_CLASSES } from './data.js';
import { parseLogic, parseLambda, parseCombinatorExpr } from './parser.js';
import { toSKI, expandToIota, formatSKI } from './compiler.js';
import { reduceLMO, evalLogicNode, stepTM, stepSRS } from './reduction.js';
import { countSymbols, getTreeMaxDepth, drawTreeCanvas } from './renderer.js';

// --- STATE MANAGEMENT ---
const state = {
  family: 'All',
  tc: 'All',
  carrier: 'All',
  query: '',
  view: 'family',
  selected: null,
  detailTab: 'anatomy',
  angle: 30,
  scale: 0.75,
  maxDepth: 12,
  theme: 'rainbow',
  layout: 'radial',
  customCombinator: '',
  lambdaInput: '\\f. \\x. f (f x)',
  logicInput: 'A & (B | ~A)',
  srsRules: 'ab -> ba',
  srsInput: 'aababb',
  tmTape: '1101',
  tmState: 'q0'
};

// --- GRAPH PAN & ZOOM STATE ---
const graphState = {
  panX: 0,
  panY: 0,
  zoomScale: 1,
  isDragging: false,
  startX: 0,
  startY: 0
};

let reductionTerm = null;
let reductionTimer = null;

// --- DOM ELEMENTS ---
const graph = document.getElementById('graph');
const cards = document.getElementById('cards');
const detailMain = document.getElementById('detailMain');
const searchInput = document.getElementById('searchInput');

function unique(arr) { return [...new Set(arr)]; }

function filteredSystems() {
  return SYSTEMS.filter(s => {
    const q = state.query.toLowerCase();
    const carrierMatch = state.carrier === 'All' || s.carriers[state.carrier];
    const tcMatch = state.tc === 'All' || (state.tc === 'Yes' ? s.turingComplete : !s.turingComplete);
    let famMatch = state.family === 'All' || s.family === state.family;
    if (state.view === 'probability' && state.family === 'Probability' && s.id === 'ISAR') {
      famMatch = true;
    }
    const textMatch = !q || [s.name, s.symbol, s.family, s.description, s.notable, s.bisimQuotient].join(' ').toLowerCase().includes(q);
    return carrierMatch && tcMatch && famMatch && textMatch;
  });
}

function renderChips() {
  const families = ['All', ...unique(SYSTEMS.map(s => s.family))];
  const tcVals = ['All', 'Yes', 'No'];
  const carriers = ['All', 'I', 'S', 'A', 'R'];
  renderChipSet('familyChips', families, state.family, val => state.family = val);
  renderChipSet('tcChips', tcVals, state.tc, val => state.tc = val);
  renderChipSet('carrierChips', carriers, state.carrier, val => state.carrier = val);
}

function renderChipSet(id, values, active, onSelect) {
  const el = document.getElementById(id);
  if (!el) return;
  el.innerHTML = '';
  values.forEach(v => {
    const b = document.createElement('button');
    b.className = 'chip' + (v === active ? ' active' : '');
    b.textContent = v;
    b.addEventListener('click', () => { onSelect(v); rerender(); });
    el.appendChild(b);
  });
}

let cachedSubstrateDistances = null;
function getSubstrateDistance(id) {
  if (!cachedSubstrateDistances) {
    cachedSubstrateDistances = { 'ISAR': 0 };
    const queue = ['ISAR'];
    const adj = {};
    SYSTEMS.forEach(s => adj[s.id] = []);
    edges.forEach(([u, v]) => {
      if (adj[u] && adj[v]) {
        adj[u].push(v);
        adj[v].push(u);
      }
    });
    while (queue.length > 0) {
      const curr = queue.shift();
      const currDist = cachedSubstrateDistances[curr];
      (adj[curr] || []).forEach(neighbor => {
        if (cachedSubstrateDistances[neighbor] === undefined) {
          cachedSubstrateDistances[neighbor] = currDist + 1;
          queue.push(neighbor);
        }
      });
    }
  }
  return cachedSubstrateDistances[id];
}

function getColor(s) {
  if (state.view === 'tc') return s.turingComplete ? '#6daa45' : '#e8af34';
  if (state.view === 'substrate') {
    const d = getSubstrateDistance(s.id);
    if (d === 0) return 'var(--color-primary)';   // Depth 0: Core substrate
    if (d === 1) return 'var(--color-blue)';      // Depth 1: Direct compile/embed neighbors
    if (d === 2) return 'var(--color-purple)';    // Depth 2: Close translation layer
    if (d === 3) return 'var(--color-red)';       // Depth 3: Extended translation layer
    if (d >= 4) return 'var(--color-orange)';     // Depth 4+: Highly remote systems
    return 'var(--color-text-faint)';             // Unreachable
  }
  if (state.view === 'quotient') return QUOTIENT_CLASSES[s.quotientClass]?.color || '#888';
  return familyColors[s.family] || s.color || '#888';
}

function renderGraph() {
  if (!graph) return;
  graph.innerHTML = '';

  const systems = filteredSystems();
  const w = graph.clientWidth || 900;
  const h = graph.clientHeight || 520;

  // Create viewport div
  const viewport = document.createElement('div');
  viewport.className = 'graph-viewport';
  viewport.id = 'graphViewport';
  viewport.style.position = 'absolute';
  viewport.style.left = '0';
  viewport.style.top = '0';
  viewport.style.width = '100%';
  viewport.style.height = '100%';
  viewport.style.transformOrigin = '0 0';
  viewport.style.transform = `translate(${graphState.panX}px, ${graphState.panY}px) scale(${graphState.zoomScale})`;
  graph.appendChild(viewport);

  // Floating zoom controls (attached directly to graph, not inside viewport)
  const controls = document.createElement('div');
  controls.className = 'zoom-controls';
  controls.style.cssText = `
    position: absolute;
    top: var(--space-3);
    right: var(--space-3);
    display: flex;
    flex-direction: column;
    gap: 6px;
    z-index: 10;
  `;
  
  const btnIn = document.createElement('button');
  btnIn.innerHTML = '＋';
  btnIn.className = 'sidebar-toggle';
  btnIn.addEventListener('click', () => {
    graphState.zoomScale = Math.min(2.5, graphState.zoomScale * 1.2);
    updateGraphTransform();
  });
  
  const btnOut = document.createElement('button');
  btnOut.innerHTML = '－';
  btnOut.className = 'sidebar-toggle';
  btnOut.addEventListener('click', () => {
    graphState.zoomScale = Math.max(0.4, graphState.zoomScale / 1.2);
    updateGraphTransform();
  });
  
  const btnReset = document.createElement('button');
  btnReset.innerHTML = '⟲';
  btnReset.className = 'sidebar-toggle';
  btnReset.addEventListener('click', () => {
    graphState.zoomScale = 1;
    graphState.panX = 0;
    graphState.panY = 0;
    updateGraphTransform();
  });
  
  controls.appendChild(btnIn);
  controls.appendChild(btnOut);
  controls.appendChild(btnReset);
  graph.appendChild(controls);

  const families = unique(systems.map(s => s.family));
  const familyY = new Map(families.map((f, i) => [f, ((i + 1) / (families.length + 1)) * h]));
  const maxPrim = Math.max(...SYSTEMS.map(s => s.primitives));
  const positions = new Map();

  // Quotient view Venn-diagram spatial arrangement
  const classKeys = Object.keys(QUOTIENT_CLASSES);
  const centerX = w / 2;
  const centerY = h / 2;
  const classCoords = {
    "Substrate":        { x: centerX,             y: centerY + h * 0.12 },
    "TuringFunctional": { x: centerX - w * 0.22,  y: centerY - h * 0.18 },
    "CCC":              { x: centerX - w * 0.04,  y: centerY - h * 0.20 },
    "Linear":           { x: centerX - w * 0.12,  y: centerY - h * 0.02 },
    "ProofTheory":      { x: centerX + w * 0.15,  y: centerY - h * 0.12 },
    "Lattice":          { x: centerX + w * 0.24,  y: centerY + h * 0.08 },
    "Process":          { x: centerX - w * 0.25,  y: centerY + h * 0.10 },
    "Rewriting":        { x: centerX - w * 0.10,  y: centerY + h * 0.20 }
  };

  const systemsInClass = {};
  systems.forEach(s => {
    if (!systemsInClass[s.quotientClass]) systemsInClass[s.quotientClass] = [];
    systemsInClass[s.quotientClass].push(s.id);
  });

  const systemsByLevel = {};
  for (let l = 0; l <= 4; l++) {
    systemsByLevel[l] = [];
  }
  systems.forEach(s => {
    const lvl = s.latticeLevel !== undefined ? s.latticeLevel : 0;
    systemsByLevel[lvl].push(s.id);
  });

  // 1. Initial coordinates assignment
  systems.forEach((s, i) => {
    if (state.view === 'quotient') {
      const pos = classCoords[s.quotientClass] || { x: centerX, y: centerY };
      const idx = systemsInClass[s.quotientClass].indexOf(s.id);
      const count = systemsInClass[s.quotientClass].length;
      const r = count > 1 ? (40 + count * 6) : 0;
      const offsetAngle = count > 1 ? (idx / count) * 2 * Math.PI : 0;
      const x = pos.x + Math.cos(offsetAngle) * r;
      const y = pos.y + Math.sin(offsetAngle) * r;
      positions.set(s.id, { x, y });
    } else if (state.view === 'probability') {
      const lvl = s.latticeLevel !== undefined ? s.latticeLevel : 0;
      const x = 100 + (lvl / 4) * (w - 200);
      const idx = systemsByLevel[lvl].indexOf(s.id);
      const count = systemsByLevel[lvl].length;
      let y;
      if (count === 1) {
        y = h / 2;
      } else {
        y = 60 + (idx / (count - 1)) * (h - 120);
      }
      positions.set(s.id, { x, y });
    } else {
      const x = 80 + ((s.primitives - 1) / Math.max(1, maxPrim - 1)) * (w - 160);
      const carrierScore = ['I', 'S', 'A', 'R'].reduce((n, k) => n + (s.carriers[k] ? 1 : 0), 0);
      const yBase = familyY.get(s.family) || h / 2;
      const y = yBase + ((carrierScore - 2) * 20) + (Math.sin(i * 1.7) * 22);
      positions.set(s.id, { x, y });
    }
  });

  // 2. Keep nodes in graph boundaries
  systems.forEach(s => {
    const pos = positions.get(s.id);
    if (pos) {
      pos.x = Math.max(50, Math.min(w - 50, pos.x));
      pos.y = Math.max(50, Math.min(h - 50, pos.y));
    }
  });

  // Draw edges (hidden in quotient view)
  edges.forEach(([a, b]) => {
    if (!positions.has(a) || !positions.has(b)) return;
    const p1 = positions.get(a), p2 = positions.get(b);
    const dx = p2.x - p1.x, dy = p2.y - p1.y;
    const len = Math.hypot(dx, dy), ang = Math.atan2(dy, dx) * 180 / Math.PI;
    const edge = document.createElement('div');
    edge.className = 'edge' + (state.view === 'quotient' ? ' hidden' : '');
    edge.style.left = p1.x + 'px';
    edge.style.top = p1.y + 'px';
    edge.style.width = len + 'px';
    edge.style.transform = `rotate(${ang}deg)`;
    viewport.appendChild(edge);
  });

  // Draw quotient boundary overlays
  if (state.view === 'quotient') {
    classKeys.forEach(key => {
      const pts = systems.filter(s => s.quotientClass === key);
      if (pts.length === 0) return; // Do not draw empty class bubbles
      
      const pos = classCoords[key];
      const count = pts.length;
      const r = count > 1 ? (40 + count * 6) : 0;
      const bubbleRadius = r + 55; // includes node circle radius + padding
      const bubbleDiameter = bubbleRadius * 2;
      
      const bubble = document.createElement('div');
      bubble.className = 'quotient-bubble visible';
      bubble.style.left = pos.x + 'px';
      bubble.style.top = pos.y + 'px';
      bubble.style.width = bubbleDiameter + 'px';
      bubble.style.height = bubbleDiameter + 'px';
      
      // Dynamic colors based on quotient class color
      const clColor = QUOTIENT_CLASSES[key]?.color || '#888';
      bubble.style.borderColor = `color-mix(in oklab, ${clColor} 40%, transparent)`;
      bubble.style.background = `color-mix(in oklab, ${clColor} 5%, transparent)`;
      
      bubble.innerHTML = `<span style="text-align:center;font-size:9.5px;font-weight:600;color:${clColor};pointer-events:none;padding:6px;max-width:90%;line-height:1.2;align-self:end;margin-bottom:8px">${QUOTIENT_CLASSES[key].name}</span>`;
      viewport.appendChild(bubble);
    });
  }

  // Draw probability axis overlays
  if (state.view === 'probability') {
    const levelNames = [
      "Poset\n(Order)",
      "Boolean Lattice\n(Classical Logic)",
      "Probability Calculus\n(Weighted Logic)",
      "Orthomodular Poset\n(Quantum Logic)",
      "Effect Algebra\n(Unsharp Logic)"
    ];
    for (let l = 0; l <= 4; l++) {
      const x = 100 + (l / 4) * (w - 200);
      const bubble = document.createElement('div');
      bubble.className = 'quotient-bubble visible';
      bubble.style.left = x + 'px';
      bubble.style.top = (h / 2) + 'px';
      bubble.style.width = '130px';
      bubble.style.height = '130px';
      bubble.style.borderStyle = 'dashed';
      bubble.style.borderColor = 'rgba(230, 126, 34, 0.4)';
      bubble.innerHTML = `<span style="text-align:center;font-size:9px;color:#e67e22;pointer-events:none;padding:5px;white-space:pre-line;text-transform:none;letter-spacing:normal">${levelNames[l]}</span>`;
      viewport.appendChild(bubble);
    }
  }

  // Draw system nodes
  systems.forEach(s => {
    const pos = positions.get(s.id);
    const node = document.createElement('button');
    node.className = 'node';
    node.style.left = pos.x + 'px';
    node.style.top = pos.y + 'px';
    node.innerHTML = `<div class="node-circle" style="background:${getColor(s)}"><span>${s.symbol}</span></div><small>${s.name}</small>`;
    node.setAttribute('aria-label', s.name);
    node.addEventListener('click', () => {
      state.customCombinator = '';
      state.selected = s.id;
      renderDetail();
      highlightSelection();
      const detailEl = document.querySelector('.detail');
      if (detailEl) {
        detailEl.scrollIntoView({ behavior: 'smooth', block: 'start' });
      }
    });
    if (state.selected && state.selected !== s.id) node.classList.add('soft');
    viewport.appendChild(node);
  });
}

function cardHTML(s) {
  return `
    <article class="card">
      <div class="card-head">
        <div>
          <h4>${s.name}</h4>
          <p class="mono">${s.symbol}</p>
        </div>
        <span class="badge" style="background:color-mix(in oklab, ${getColor(s)} 15%, transparent);color:${getColor(s)}">${s.family}</span>
      </div>
      <p>${s.description}</p>
      <div class="metric-grid">
        <div class="metric"><strong>${s.primitives}</strong><span>Primitives</span></div>
        <div class="metric"><strong>${s.turingComplete ? 'Yes' : 'No'}</strong><span>Turing-complete</span></div>
      </div>
      <div class="carrier-grid">
        ${['I', 'S', 'A', 'R'].map(k => `<div class="carrier ${s.carriers[k] ? 'on' : ''}">${k}</div>`).join('')}
      </div>
      <div class="rules">${s.rewriteRules.slice(0, 3).map(r => `<span class="rule">${r}</span>`).join('')}</div>
    </article>`;
}

function renderCards() {
  if (!cards) return;
  const systems = filteredSystems();
  cards.innerHTML = systems.map(cardHTML).join('');
  [...cards.children].forEach((card, i) => {
    card.addEventListener('click', () => {
      state.customCombinator = '';
      state.selected = systems[i].id;
      renderDetail();
      highlightSelection();
      const detailEl = document.querySelector('.detail');
      if (detailEl) {
        detailEl.scrollIntoView({ behavior: 'smooth', block: 'start' });
      }
    });
  });
}

function renderDetail() {
  if (!detailMain) return;

  // Clear any running reduction sandbox timer when switching specimen/detail views
  if (reductionTimer) {
    clearInterval(reductionTimer);
    reductionTimer = null;
  }

  const s = SYSTEMS.find(x => x.id === state.selected);
  if (!s) {
    detailMain.innerHTML = `
      <div class="detail-empty">
        <div>
          <p>Select a system from the graph or cards.</p>
          <p style="font-size:var(--text-sm)">Use the tabs in the detail panel to inspect the system's local anatomy, translation maps, and interactive execution environments.</p>
        </div>
      </div>`;
    return;
  }
  const neighbors = edges.flatMap(([a, b]) => a === s.id ? [b] : (b === s.id ? [a] : [])).map(id => SYSTEMS.find(x => x.id === id)).filter(Boolean);

  detailMain.innerHTML = `
    <div style="display:grid;gap:var(--space-5)">
      <div class="tab-headers">
        <button class="tab-btn ${state.detailTab === 'anatomy' ? 'active' : ''}" id="tabBtnAnatomy" data-tab="anatomy">Anatomy</button>
        <button class="tab-btn ${state.detailTab === 'lab' ? 'active' : ''}" id="tabBtnLab" data-tab="lab">Interactive Lab</button>
        <button class="tab-btn ${state.detailTab === 'occam' ? 'active' : ''}" id="tabBtnOccam" data-tab="occam">Occam Lens</button>
      </div>
      <div id="anatomyContent" style="display:${state.detailTab === 'anatomy' ? 'block' : 'none'}">
        <div style="display:grid;gap:var(--space-5)">
          <div class="card-head">
            <div>
              <h3 style="font-family:var(--font-display);font-size:var(--text-2xl)">${s.name}</h3>
              <p class="mono">${s.symbol} · ${s.family}</p>
            </div>
            <span class="badge" style="background:color-mix(in oklab, ${getColor(s)} 15%, transparent);color:${getColor(s)}">${s.turingComplete ? 'Universal' : 'Normalizing / decidable'}</span>
          </div>
          <p>${s.description}</p>
          <div class="metric-grid">
            <div class="metric"><strong>${s.primitives}</strong><span>Primitive basis size</span></div>
            <div class="metric"><strong>${s.bisimQuotient}</strong><span>Behavioral quotient</span></div>
            <div class="metric"><strong>${s.encoding}</strong><span>Typical encoding</span></div>
            <div class="metric"><strong>${s.notable}</strong><span>Why it matters</span></div>
          </div>
          <div>
            <h4 style="margin-bottom:var(--space-3)">Carrier fingerprint</h4>
            <div class="carrier-grid">${['I', 'S', 'A', 'R'].map(k => `<div class="carrier ${s.carriers[k] ? 'on' : ''}">${k}</div>`).join('')}</div>
          </div>
          <div>
            <h4 style="margin-bottom:var(--space-3)">Rewrite laws</h4>
            <div class="rules">${s.rewriteRules.map(r => `<span class="rule">${r}</span>`).join('')}</div>
          </div>
          <div>
            <h4 style="margin-bottom:var(--space-3)">Zoo neighbors</h4>
            <div class="rules">${neighbors.length ? neighbors.map(n => `<span class="rule">${n.name}</span>`).join('') : '<span class="rule">No direct neighbor listed</span>'}</div>
          </div>
        </div>
      </div>
      <div id="labContent" style="display:${state.detailTab === 'lab' ? 'block' : 'none'}"></div>
      <div id="occamContent" style="display:${state.detailTab === 'occam' ? 'block' : 'none'}"></div>
    </div>`;

  const btnAnatomy = document.getElementById('tabBtnAnatomy');
  const btnLab = document.getElementById('tabBtnLab');
  const btnOccam = document.getElementById('tabBtnOccam');
  const divAnatomy = document.getElementById('anatomyContent');
  const divLab = document.getElementById('labContent');
  const divOccam = document.getElementById('occamContent');

  btnAnatomy.addEventListener('click', () => {
    state.detailTab = 'anatomy';
    btnAnatomy.classList.add('active');
    btnLab.classList.remove('active');
    btnOccam.classList.remove('active');
    divAnatomy.style.display = 'block';
    divLab.style.display = 'none';
    divOccam.style.display = 'none';
    if (reductionTimer) {
      clearInterval(reductionTimer);
      reductionTimer = null;
    }
  });

  btnLab.addEventListener('click', () => {
    state.detailTab = 'lab';
    btnLab.classList.add('active');
    btnAnatomy.classList.remove('active');
    btnOccam.classList.remove('active');
    divAnatomy.style.display = 'none';
    divLab.style.display = 'block';
    divOccam.style.display = 'none';
    renderLab(s);
  });

  btnOccam.addEventListener('click', () => {
    state.detailTab = 'occam';
    btnOccam.classList.add('active');
    btnAnatomy.classList.remove('active');
    btnLab.classList.remove('active');
    divAnatomy.style.display = 'none';
    divLab.style.display = 'none';
    divOccam.style.display = 'block';
    renderOccamLens(s);
  });

  if (state.detailTab === 'lab') {
    renderLab(s);
  } else if (state.detailTab === 'occam') {
    renderOccamLens(s);
  }
}

function renderLab(s) {
  const container = document.getElementById('labContent');
  if (!container) return;
  container.innerHTML = '';

  if (reductionTimer) {
    clearInterval(reductionTimer);
    reductionTimer = null;
  }

  if (s.family === 'Combinator') {
    const initialExpr = s.encoding;
    
    let presets = [];
    let defaultExpr = '';
    if (s.id === 'iota' || s.id.startsWith('barker-')) {
      if (s.id === 'iota') {
        presets = [
          { value: 'ι x', label: 'ι x (Expand ι)' },
          { value: 'ι ι x', label: 'ι ι x' },
          { value: 'ι (ι ι) x', label: 'ι (ι ι) x' }
        ];
        defaultExpr = 'ι x';
      } else {
        presets = [
          { value: `${s.encoding} x`, label: `${s.name} applied` },
          { value: `${s.encoding}`, label: `${s.name} definition` }
        ];
        defaultExpr = s.encoding;
      }
    } else if (s.id === 'SK') {
      presets = [
        { value: 'S K K x', label: 'S K K x (Identity)' },
        { value: 'S (K S) K x y z', label: 'S (K S) K x y z (Composition B)' },
        { value: 'S K K (S K K)', label: 'S K K (S K K) (Divergent Omega)' }
      ];
      defaultExpr = 'S K K x';
    } else if (s.id === 'BCKW') {
      presets = [
        { value: 'I x', label: 'I x (Identity)' },
        { value: 'B I I x', label: 'B I I x (Double application)' },
        { value: 'W I x', label: 'W I x (Duplication)' },
        { value: 'C I x y', label: 'C I x y (Flip identity)' },
        { value: 'K x y', label: 'K x y (Constant)' }
      ];
      defaultExpr = 'B I I x';
    } else {
      presets = [
        { value: 'S I I x', label: 'S I I x (Double application)' },
        { value: 'S(KS)K x y z', label: 'S(KS)K x y z (Composition B)' },
        { value: 'I x', label: 'I x (Identity)' },
        { value: 'K x y', label: 'K x y (Constant)' },
        { value: 'S I I (S I I)', label: 'S I I (S I I) (Divergent Omega)' }
      ];
      defaultExpr = 'S I I x';
    }

    container.innerHTML = `
      <div class="lab-container">
        <h4>Iota Tree Visualizer</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          This renders the combinator <strong>${s.name}</strong> expanded into Barker's Iota primitives as a binary tree.
        </p>
        <div class="canvas-card">
          <canvas id="treeCanvas" width="480" height="360"></canvas>
        </div>
        <div class="controls-grid">
          <div class="control-item">
            <label>Layout</label>
            <select id="layoutSelect">
              <option value="radial" ${state.layout === 'radial' ? 'selected' : ''}>Radial Mandala</option>
              <option value="topdown" ${state.layout === 'topdown' ? 'selected' : ''}>Tidy Top-Down</option>
            </select>
          </div>
          <div class="control-item">
            <label>Branch Angle (${state.angle}°)</label>
            <input type="range" id="angleRange" min="5" max="90" value="${state.angle}" />
          </div>
          <div class="control-item">
            <label>Scale Factor (${state.scale})</label>
            <input type="range" id="scaleRange" min="0.5" max="0.95" step="0.05" value="${state.scale}" />
          </div>
          <div class="control-item">
            <label>Color Palette</label>
            <select id="themeSelect">
              <option value="rainbow" ${state.theme === 'rainbow' ? 'selected' : ''}>Rainbow</option>
              <option value="emerald" ${state.theme === 'emerald' ? 'selected' : ''}>Emerald</option>
              <option value="cyberpunk" ${state.theme === 'cyberpunk' ? 'selected' : ''}>Cyberpunk</option>
              <option value="monochrome" ${state.theme === 'monochrome' ? 'selected' : ''}>Monochrome</option>
            </select>
          </div>
        </div>
        
        <div style="display:grid;gap:var(--space-2)">
          <label style="font-size:var(--text-sm);font-weight:700">Test Custom Combinator Expression</label>
          <div style="display:flex;gap:var(--space-2)">
            <input type="text" id="customCombInput" class="control-item" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm)" placeholder="e.g. S(KS)K or S(BBS)(KK)" value="${state.customCombinator || initialExpr}" />
            <button id="renderCustomBtn" class="toggle active" style="padding:0 var(--space-4)">Render</button>
          </div>
          <p id="combError" style="color:var(--color-red);font-size:var(--text-sm);display:none"></p>
          <div class="metric-grid" style="margin-top:5px">
            <div class="metric"><strong id="combSizeVal">-</strong><span>Iota Symbol Count</span></div>
            <div class="metric"><strong id="combDepthVal">-</strong><span>Tree Depth</span></div>
          </div>
        </div>

        <div style="border-top:1px solid color-mix(in oklab, var(--color-text) 10%, transparent);padding-top:var(--space-4);margin-top:var(--space-4);display:grid;gap:var(--space-3)">
          <h4 style="font-size:var(--text-md)">Reduction Sandbox</h4>
          <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
            Step through active reductions of combinators containing variables (like <code>x, y, z</code>).
          </p>
          <div style="display:flex;gap:var(--space-2)">
            <select id="reductionPresetSelect" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);color:var(--color-text);font-size:var(--text-sm)">
              ${presets.map(p => `<option value="${p.value}">${p.label}</option>`).join('')}
            </select>
            <button id="reductionResetBtn" class="toggle active" style="padding:0 var(--space-3)">Load</button>
          </div>
          
          <div style="display:flex;gap:var(--space-2)">
            <input type="text" id="reductionExprInput" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);font-family:monospace;font-size:var(--text-sm)" value="${defaultExpr}" />
            <button id="reductionStepBtn" class="toggle" style="padding:0 var(--space-3)">Step</button>
            <button id="reductionRunBtn" class="toggle" style="padding:0 var(--space-3)">Run</button>
          </div>
          
          <div class="trace-box" id="reductionTraceBox" style="max-height:100px">Load an expression to start reduction trace...</div>
        </div>
      </div>`;

    const canvas = document.getElementById('treeCanvas');
    
    function updateTree() {
      const expr = document.getElementById('customCombInput').value.trim() || initialExpr;
      const errorEl = document.getElementById('combError');
      if (!errorEl) return;
      errorEl.style.display = 'none';
      try {
        const parsed = parseCombinatorExpr(expr);
        const expanded = expandToIota(parsed);
        
        drawTreeCanvas(canvas, expanded, state);
        
        const size = countSymbols(expanded);
        const depth = getTreeMaxDepth(expanded);
        document.getElementById('combSizeVal').textContent = size;
        document.getElementById('combDepthVal').textContent = depth;
      } catch (err) {
        errorEl.textContent = `Error: ${err.message}`;
        errorEl.style.display = 'block';
      }
    }

    updateTree();

    document.getElementById('layoutSelect').addEventListener('change', e => {
      state.layout = e.target.value;
      updateTree();
    });
    document.getElementById('themeSelect').addEventListener('change', e => {
      state.theme = e.target.value;
      updateTree();
    });
    document.getElementById('angleRange').addEventListener('input', e => {
      state.angle = parseInt(e.target.value);
      e.target.parentElement.querySelector('label').textContent = `Branch Angle (${state.angle}°)`;
      updateTree();
    });
    document.getElementById('scaleRange').addEventListener('input', e => {
      state.scale = parseFloat(e.target.value);
      e.target.parentElement.querySelector('label').textContent = `Scale Factor (${state.scale})`;
      updateTree();
    });
    document.getElementById('renderCustomBtn').addEventListener('click', () => {
      state.customCombinator = document.getElementById('customCombInput').value.trim();
      updateTree();
    });
    document.getElementById('customCombInput').addEventListener('keypress', e => {
      if (e.key === 'Enter') {
        state.customCombinator = e.target.value.trim();
        updateTree();
      }
    });

    // --- REDUCTION SANDBOX EVENT LISTENERS & STATE ---
    function loadReduction() {
      if (reductionTimer) {
        clearInterval(reductionTimer);
        reductionTimer = null;
        document.getElementById('reductionRunBtn').textContent = 'Run';
        document.getElementById('reductionRunBtn').classList.remove('active');
      }
      const exprStr = document.getElementById('reductionExprInput').value.trim();
      const traceEl = document.getElementById('reductionTraceBox');
      traceEl.textContent = '';
      try {
        reductionTerm = parseCombinatorExpr(exprStr);
        traceEl.textContent += `Loaded expression: ${formatSKI(reductionTerm)}\n`;
        updateReductionTree();
      } catch (err) {
        traceEl.textContent = `Error loading: ${err.message}\n`;
      }
    }

    function updateReductionTree() {
      if (!reductionTerm) return;
      const expanded = expandToIota(reductionTerm);
      drawTreeCanvas(canvas, expanded, state);
      
      const size = countSymbols(expanded);
      const depth = getTreeMaxDepth(expanded);
      document.getElementById('combSizeVal').textContent = size;
      document.getElementById('combDepthVal').textContent = depth;
      document.getElementById('customCombInput').value = formatSKI(reductionTerm);
    }

    function stepReduction() {
      if (!reductionTerm) return;
      const traceEl = document.getElementById('reductionTraceBox');
      const prevStr = formatSKI(reductionTerm);
      const res = reduceLMO(reductionTerm);
      if (res.reduced) {
        reductionTerm = res.node;
        const newStr = formatSKI(reductionTerm);
        traceEl.textContent += `${prevStr}  →  ${newStr}\n`;
        traceEl.scrollTop = traceEl.scrollHeight;
        updateReductionTree();
      } else {
        traceEl.textContent += `Normal form reached: ${prevStr}\n`;
        traceEl.scrollTop = traceEl.scrollHeight;
        if (reductionTimer) {
          clearInterval(reductionTimer);
          reductionTimer = null;
          document.getElementById('reductionRunBtn').textContent = 'Run';
          document.getElementById('reductionRunBtn').classList.remove('active');
        }
      }
    }

    function toggleRunReduction() {
      const btn = document.getElementById('reductionRunBtn');
      if (reductionTimer) {
        clearInterval(reductionTimer);
        reductionTimer = null;
        btn.textContent = 'Run';
        btn.classList.remove('active');
      } else {
        btn.textContent = 'Pause';
        btn.classList.add('active');
        reductionTimer = setInterval(stepReduction, 800);
      }
    }

    document.getElementById('reductionPresetSelect').addEventListener('change', e => {
      document.getElementById('reductionExprInput').value = e.target.value;
      loadReduction();
    });
    document.getElementById('reductionResetBtn').addEventListener('click', loadReduction);
    document.getElementById('reductionStepBtn').addEventListener('click', stepReduction);
    document.getElementById('reductionRunBtn').addEventListener('click', toggleRunReduction);
    
    loadReduction();

  } else if (s.family === 'Lambda') {
    container.innerHTML = `
      <div class="lab-container">
        <h4>Translation Lab (λ → SKI → Iota)</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Compile λ-calculus terms into optimized SKI combinators (using abstraction elimination with η-contraction), then expand to a binary Iota tree.
        </p>
        <div style="display:grid;gap:var(--space-2)">
          <label style="font-size:var(--text-xs);font-weight:700">Enter Lambda Term (use \\ or λ for abstraction)</label>
          <div style="display:flex;gap:var(--space-2)">
            <input type="text" id="lambdaInput" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);font-family:monospace" value="${state.lambdaInput}" placeholder="e.g. \\f. \\x. f (f x)" />
            <button id="compileBtn" class="toggle active" style="padding:0 var(--space-4)">Compile</button>
          </div>
          <p id="lambdaError" style="color:var(--color-red);font-size:var(--text-sm);display:none"></p>
        </div>
        
        <div class="trace-box" id="compileTrace">Compilation ready...</div>

        <div class="canvas-card" id="lambdaCanvasContainer" style="display:none">
          <canvas id="lambdaTreeCanvas" width="480" height="300"></canvas>
        </div>
        
        <div class="metric-grid" id="lambdaMetrics" style="display:none">
          <div class="metric"><strong id="lambdaSizeVal">-</strong><span>Iota Symbol Count</span></div>
          <div class="metric"><strong id="lambdaDepthVal">-</strong><span>Iota Tree Depth</span></div>
        </div>
      </div>
    `;

    const traceBox = document.getElementById('compileTrace');
    const lambdaCanvasContainer = document.getElementById('lambdaCanvasContainer');
    const lambdaMetrics = document.getElementById('lambdaMetrics');
    const canvas = document.getElementById('lambdaTreeCanvas');

    function compile() {
      const val = document.getElementById('lambdaInput').value.trim();
      state.lambdaInput = val;
      const errorEl = document.getElementById('lambdaError');
      errorEl.style.display = 'none';
      traceBox.textContent = '';
      lambdaCanvasContainer.style.display = 'none';
      lambdaMetrics.style.display = 'none';

      try {
        traceBox.textContent += `1. Parsing lambda term: "${val}"\n`;
        const parsed = parseLambda(val);
        
        traceBox.textContent += `2. Performing Abstraction Elimination (with η-contraction)...\n`;
        const skiNode = toSKI(parsed);
        const skiStr = formatSKI(skiNode);
        traceBox.textContent += `   → Compiled SKI term: ${skiStr}\n`;

        traceBox.textContent += `3. Expanding SKI to Iota primitives...\n`;
        const iotaNode = expandToIota(skiNode);
        const size = countSymbols(iotaNode);
        const depth = getTreeMaxDepth(iotaNode);
        
        traceBox.textContent += `   → Successfully compiled to Iota tree!\n`;
        traceBox.textContent += `   → Total size: ${size} symbols, Depth: ${depth}\n`;

        lambdaCanvasContainer.style.display = 'grid';
        lambdaMetrics.style.display = 'grid';
        document.getElementById('lambdaSizeVal').textContent = size;
        document.getElementById('lambdaDepthVal').textContent = depth;

        drawTreeCanvas(canvas, iotaNode, state);
      } catch (err) {
        errorEl.textContent = `Compilation Error: ${err.message}`;
        errorEl.style.display = 'block';
        traceBox.textContent += `\n[FATAL ERROR] Compilation failed: ${err.message}\n`;
      }
    }

    compile();

    document.getElementById('compileBtn').addEventListener('click', compile);
    document.getElementById('lambdaInput').addEventListener('keypress', e => {
      if (e.key === 'Enter') compile();
    });

  } else if (s.id === 'prop-logic') {
    container.innerHTML = `
      <div class="lab-container">
        <h4>Truth Table Sandbox</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Evaluate propositional logic expressions. Use upper-case letters for variables, <code>&</code> for AND, <code>|</code> for OR, <code>~</code> for NOT, and <code>=></code> for implication.
        </p>
        <div style="display:flex;gap:var(--space-2)">
          <input type="text" id="logicInput" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);font-family:monospace" value="${state.logicInput}" placeholder="e.g. A & (B | ~A)" />
          <button id="logicEvalBtn" class="toggle active" style="padding:0 var(--space-4)">Evaluate</button>
        </div>
        <p id="logicError" style="color:var(--color-red);font-size:var(--text-sm);display:none"></p>
        <div id="truthTableContainer" style="overflow-x:auto;max-height:240px;border:1px solid var(--color-border);border-radius:var(--radius-lg);background:#0d0c0a"></div>
      </div>
    `;

    function generateTruthTable() {
      const val = document.getElementById('logicInput').value.trim();
      state.logicInput = val;
      const errorEl = document.getElementById('logicError');
      const tableContainer = document.getElementById('truthTableContainer');
      errorEl.style.display = 'none';
      tableContainer.innerHTML = '';

      try {
        const ast = parseLogic(val);
        const varsSet = new Set();
        function collectVars(node) {
          if (node.type === 'var') varsSet.add(node.name);
          else if (node.type === 'not') collectVars(node.body);
          else if (node.left && node.right) {
            collectVars(node.left);
            collectVars(node.right);
          }
        }
        collectVars(ast);
        const vars = Array.from(varsSet).sort();

        if (vars.length > 5) {
          throw new Error("Too many variables (maximum 5 for table rendering).");
        }

        let tableHTML = `<table style="width:100%;border-collapse:collapse;font-size:var(--text-sm)">
          <thead>
            <tr style="border-bottom:1px solid var(--color-border);background:var(--color-surface-2)">
              ${vars.map(v => `<th style="padding:8px;text-align:center">${v}</th>`).join('')}
              <th style="padding:8px;text-align:center;color:var(--color-primary)">${val}</th>
            </tr>
          </thead>
          <tbody>`;

        for (let i = 0; i < Math.pow(2, vars.length); i++) {
          const env = {};
          vars.forEach((v, index) => {
            env[v] = ((i >> (vars.length - 1 - index)) & 1) === 1;
          });

          const result = evalLogicNode(ast, env);
          tableHTML += `<tr style="border-bottom:1px solid color-mix(in oklab, var(--color-border) 40%, transparent)">
            ${vars.map(v => `<td style="padding:8px;text-align:center;color:${env[v] ? 'var(--color-green)' : 'var(--color-red)'}">${env[v] ? 'T' : 'F'}</td>`).join('')}
            <td style="padding:8px;text-align:center;font-weight:bold;color:${result ? 'var(--color-green)' : 'var(--color-red)'}">${result ? 'T' : 'F'}</td>
          </tr>`;
        }
        tableHTML += `</tbody></table>`;
        tableContainer.innerHTML = tableHTML;
      } catch (err) {
        errorEl.textContent = `Error: ${err.message}`;
        errorEl.style.display = 'block';
      }
    }

    generateTruthTable();
    document.getElementById('logicEvalBtn').addEventListener('click', generateTruthTable);
    document.getElementById('logicInput').addEventListener('keypress', e => {
      if (e.key === 'Enter') generateTruthTable();
    });

  } else if (s.id === 'turing-machine') {
    container.innerHTML = `
      <div class="lab-container">
        <h4>Turing Machine Simulator (Binary Incrementer)</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          This Turing Machine increments a binary number.
          State <code>q0</code> finds the right end of the number, then state <code>q1</code> performs the carry propagation (replacing 1s with 0s and the first 0 with a 1) and halts.
        </p>
        <div style="display:flex;gap:var(--space-2);align-items:center">
          <input type="text" id="tmTapeInput" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);font-family:monospace" value="${state.tmTape}" placeholder="e.g. 1101" />
          <button id="tmResetBtn" class="toggle" style="padding:var(--space-2) var(--space-4)">Reset</button>
          <button id="tmStepBtn" class="toggle active" style="padding:var(--space-2) var(--space-4)">Step</button>
        </div>
        
        <div style="display:flex;gap:4px;overflow-x:auto;padding:var(--space-4);background:#0d0c0a;border-radius:var(--radius-lg);border:1px solid var(--color-border);margin:10px 0" id="tmTapeView">
        </div>

        <div class="trace-box" id="tmTraceBox">Transition rules trace...</div>
      </div>
    `;

    let tmTapeArr = state.tmTape.split('');
    let tmHead = 0;
    let tmState = 'q0';
    const tapeView = document.getElementById('tmTapeView');
    const traceBox = document.getElementById('tmTraceBox');

    function renderTMTape() {
      tapeView.innerHTML = '';
      const minIdx = Math.min(0, tmHead - 2);
      const maxIdx = Math.max(tmTapeArr.length - 1, tmHead + 2);
      
      for (let i = minIdx - 1; i <= maxIdx + 1; i++) {
        const char = tmTapeArr[i] === undefined ? 'B' : tmTapeArr[i];
        const isHead = i === tmHead;
        const cell = document.createElement('div');
        cell.style.cssText = `
          min-width: 32px;
          height: 32px;
          border: 1px solid ${isHead ? 'var(--color-primary)' : 'var(--color-border)'};
          background: ${isHead ? 'color-mix(in oklab, var(--color-primary) 20%, #171614)' : '#171614'};
          display: grid;
          place-items: center;
          font-family: monospace;
          font-weight: bold;
          border-radius: 4px;
          position: relative;
          color: ${char === 'B' ? 'var(--color-text-faint)' : 'var(--color-text)'};
        `;
        cell.textContent = char;
        if (isHead) {
          const headLabel = document.createElement('span');
          headLabel.style.cssText = 'position:absolute;bottom:-18px;font-size:9px;color:var(--color-primary)';
          headLabel.textContent = tmState;
          cell.appendChild(headLabel);
        }
        tapeView.appendChild(cell);
      }
    }

    renderTMTape();

    document.getElementById('tmResetBtn').addEventListener('click', () => {
      const tapeInput = document.getElementById('tmTapeInput').value.trim() || '1101';
      state.tmTape = tapeInput;
      tmTapeArr = tapeInput.split('');
      tmHead = 0;
      tmState = 'q0';
      traceBox.textContent = 'Reset completed. State = q0, Head at index 0.\n';
      renderTMTape();
    });

    document.getElementById('tmStepBtn').addEventListener('click', () => {
      if (tmState === 'q_halt') {
        traceBox.textContent += 'Machine already halted!\n';
        return;
      }
      const res = stepTM(tmTapeArr, tmHead, tmState);
      tmTapeArr = res.tape;
      tmHead = res.head;
      tmState = res.state;
      traceBox.textContent += `${res.rule}\n`;
      traceBox.scrollTop = traceBox.scrollHeight;
      renderTMTape();
    });

  } else if (s.id === 'string-rewriting') {
    container.innerHTML = `
      <div class="lab-container">
        <h4>Semi-Thue String Rewriting Sandbox</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Specify production rules (one per line, e.g. <code>ab -> ba</code> or <code>a -> b</code>) and a starting string, then run the rewriting steps.
        </p>
        <div class="controls-grid" style="grid-template-columns: 1fr">
          <div class="control-item">
            <label>Production Rules (LHS -> RHS)</label>
            <textarea id="srsRulesInput" style="height:60px;background:var(--color-surface);border:1px solid var(--color-border);border-radius:var(--radius-sm);padding:var(--space-2);color:var(--color-text);font-family:monospace">${state.srsRules}</textarea>
          </div>
        </div>
        
        <div style="display:flex;gap:var(--space-2);align-items:center">
          <input type="text" id="srsInput" style="flex:1;background:var(--color-surface-2);border:1px solid var(--color-border);padding:var(--space-2);border-radius:var(--radius-sm);font-family:monospace" value="${state.srsInput}" placeholder="Initial string" />
          <button id="srsResetBtn" class="toggle" style="padding:var(--space-2) var(--space-4)">Reset</button>
          <button id="srsStepBtn" class="toggle active" style="padding:var(--space-2) var(--space-4)">Step</button>
        </div>

        <div class="trace-box" id="srsTraceBox">Rewriting trace...</div>
      </div>
    `;

    let currentStr = state.srsInput;
    const traceBox = document.getElementById('srsTraceBox');

    document.getElementById('srsResetBtn').addEventListener('click', () => {
      const inputVal = document.getElementById('srsInput').value.trim() || 'aababb';
      state.srsInput = inputVal;
      state.srsRules = document.getElementById('srsRulesInput').value.trim();
      currentStr = inputVal;
      traceBox.textContent = `Reset completed. Initial string: "${currentStr}"\n`;
    });

    document.getElementById('srsStepBtn').addEventListener('click', () => {
      const rulesVal = document.getElementById('srsRulesInput').value.trim();
      const res = stepSRS(rulesVal, currentStr);
      if (res.success) {
        traceBox.textContent += `Step: Apply rule [${res.rule}]  →  "${res.output}"\n`;
        currentStr = res.output;
      } else {
        traceBox.textContent += `Halt: No matching rules can be applied.\n`;
      }
      traceBox.scrollTop = traceBox.scrollHeight;
    });

  } else {
    let contentHTML = '';
    if (s.id === 'coc' || s.id === 'coq' || s.id === 'lean') {
      contentHTML = `
        <h4>Dependent Type Translation Witness</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Calculus of Constructions (CoC) terms compile directly into modern proof assistants (Coq & Lean) via type-theoretic correspondence.
        </p>
        <div class="trace-box" style="height:auto;max-height:none">
// 1. Polymorphic Identity Function
[CoC]   λ(X:Type). λ(x:X). x  :  Π(X:Type). X → X

[Coq]   Definition id : forall (X : Type), X -> X :=
          fun (X : Type) (x : X) => x.

[Lean]  def id (X : Type) (x : X) : X := x

// 2. Church Encoding of Natural Numbers (Double function application)
[CoC]   λ(X:Type). λ(f:X→X). λ(x:X). f (f x)

[Coq]   Definition two : forall (X : Type), (X -> X) -> X -> X :=
          fun (X : Type) (f : X -> X) (x : X) => f (f x).

[Lean]  def two (X : Type) (f : X → X) (x : X) : X := f (f x)
        </div>
      `;
    } else if (s.id === 'pi-calculus' || s.id === 'ccs') {
      contentHTML = `
        <h4>Process Calculus Encoding Witness</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Milner's Calculus of Communicating Systems (CCS) can be translated into the π-calculus by expressing channel synchronization as dummy value communication.
        </p>
        <div class="trace-box" style="height:auto;max-height:none">
// CCS Prefix and Parallel Composition
[CCS]   a.P | ā.Q  →τ  P | Q   (synchronous action)

// π-calculus Translation:
// Translate CCS actions into π-calculus where we pass a dummy name 'c'
[π]     a(x).[[P]] | ā⟨c⟩.[Q]]  →  [[P]] | [[Q]]  (where x is a dummy variable)

// Full translation mapping:
[[ 0 ]]           =  0
[[ a.P ]]         =  a(x).[[P]]
[[ ā.P ]]         =  ā⟨c⟩.[[P]]
[[ P | Q ]]       =  [[P]] | [[Q]]
[[ (νa) P ]]      =  (νa) [[P]]
        </div>
      `;
    } else if (s.id === 'isabelle-isar' || s.id === 'sequent-calculus') {
      contentHTML = `
        <h4>Isar Structured Proof & Sequent Calculus Alignment</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          Isar proofs compile proof obligations into sequent-calculus style deductions.
        </p>
        <div class="trace-box" style="height:auto;max-height:none">
// Logical Sequent: A ∧ B ⊢ B ∧ A
[Sequent]  
   A, B ⊢ B     A, B ⊢ A
  ----------------------- (∧-Intro)
   A, B ⊢ B ∧ A
  ----------------- (∧-Left)
   A ∧ B ⊢ B ∧ A

// Isabelle/Isar structured equivalent:
lemma conj_commute: "A & B ==> B & A"
proof -
  assume "A & B"
  then have "A" and "B" by (rule conjE)+
  then show "B & A" by (rule conjI)
qed
        </div>
      `;
    } else {
      contentHTML = `
        <h4>Anatomy & Carriers Sandbox</h4>
        <p style="font-size:var(--text-sm);color:var(--color-text-muted)">
          This system realized the carrier roles: <strong>${Object.keys(s.carriers).filter(k => s.carriers[k]).join(', ')}</strong>.
        </p>
        <div class="trace-box" style="height:auto;max-height:none">
System ID: ${s.id}
Family: ${s.family}
Turing-Complete: ${s.turingComplete ? 'Yes' : 'No'}
Primitives Basis Size: ${s.primitives}
Semantics Style: ${s.encoding}
        </div>
      `;
    }
    container.innerHTML = `<div class="lab-container">${contentHTML}</div>`;
  }
}

function renderOccamLens(s) {
  const container = document.getElementById('occamContent');
  if (!container) return;
  
  const pCount = s.occam?.parameterCount || "0 (No parameters)";
  const pVol = s.occam?.parameterVolume || "None (Discrete system)";
  const flex = s.occam?.flexibility || "Strictly bounded";
  const comp = s.occam?.compressionLength || "Minimal";
  const marg = s.occam?.marginalLikelihood || "Maximum evidence (unparameterized)";

  container.innerHTML = `
    <div class="lab-container">
      <h4 style="margin-bottom:var(--space-2)">Bayesian Evidence & Occam Penalty Profile</h4>
      <p style="font-size:var(--text-sm);color:var(--color-text-muted);margin-bottom:var(--space-4)">
        A specimen's Bayesian evidence (marginal likelihood) scores its validity against observed data \\(D\\):
      </p>
      
      <div style="padding:var(--space-4); background:var(--color-surface-offset); border-radius:var(--radius-md); border:1px solid var(--color-border); margin-bottom:var(--space-4); text-align:center; font-family:var(--font-mono); font-size:var(--text-lg); color:var(--color-primary)">
        \\[p(D \\mid M) = \\int p(D \\mid \\theta, M) p(\\theta \\mid M) d\\theta\\]
      </div>
      
      <p style="font-size:var(--text-sm);color:var(--color-text-muted);margin-bottom:var(--space-5)">
        The penalty arises because highly flexible models spread their prior probability mass \\(p(\\theta \\mid M)\\) over a large parameter volume, leaving less mass for the specific parameters that match the data.
      </p>
      
      <div style="display:grid;grid-template-columns:1fr;gap:var(--space-3)">
        <div style="background:var(--color-surface-2);padding:var(--space-4);border:1px solid var(--color-border);border-radius:var(--radius-md)">
          <strong style="color:var(--color-purple);font-size:var(--text-sm);display:block;margin-bottom:4px">Parameter Count</strong>
          <span style="font-size:var(--text-sm);color:var(--color-text)">${pCount}</span>
        </div>
        <div style="background:var(--color-surface-2);padding:var(--space-4);border:1px solid var(--color-border);border-radius:var(--radius-md)">
          <strong style="color:var(--color-purple);font-size:var(--text-sm);display:block;margin-bottom:4px">Prior Volume / Range</strong>
          <span style="font-size:var(--text-sm);color:var(--color-text)">${pVol}</span>
        </div>
        <div style="background:var(--color-surface-2);padding:var(--space-4);border:1px solid var(--color-border);border-radius:var(--radius-md)">
          <strong style="color:var(--color-purple);font-size:var(--text-sm);display:block;margin-bottom:4px">Expressive Flexibility</strong>
          <span style="font-size:var(--text-sm);color:var(--color-text)">${flex}</span>
        </div>
        <div style="background:var(--color-surface-2);padding:var(--space-4);border:1px solid var(--color-border);border-radius:var(--radius-md)">
          <strong style="color:var(--color-purple);font-size:var(--text-sm);display:block;margin-bottom:4px">Compression Length</strong>
          <span style="font-size:var(--text-sm);color:var(--color-text)">${comp}</span>
        </div>
        <div style="background:var(--color-surface-2);padding:var(--space-4);border:1px solid var(--color-border);border-radius:var(--radius-md)">
          <strong style="color:var(--color-purple);font-size:var(--text-sm);display:block;margin-bottom:4px">Marginal Likelihood (Occam Score)</strong>
          <span style="font-size:var(--text-sm);color:var(--color-text)">${marg}</span>
        </div>
      </div>
    </div>
  `;
  
  if (window.MathJax) {
    window.MathJax.typesetPromise([container]).catch(err => console.log('MathJax typesetting error:', err));
  }
}

function highlightSelection() {
  if (!graph) return;
  [...graph.querySelectorAll('.node')].forEach((n, i) => {
    const systems = filteredSystems();
    const s = systems[i];
    if (!s) return;
    n.style.opacity = !state.selected || s.id === state.selected ? '1' : '.35';
  });
}

function renderStats() {
  const statSys = document.getElementById('statSystems');
  const statFam = document.getElementById('statFamilies');
  const statTC = document.getElementById('statTC');
  if (statSys) statSys.textContent = SYSTEMS.length;
  if (statFam) statFam.textContent = unique(SYSTEMS.map(s => s.family)).length;
  if (statTC) statTC.textContent = SYSTEMS.filter(s => s.turingComplete).length;
}

function rerender() {
  renderChips();
  renderGraph();
  renderCards();
  renderDetail();
  highlightSelection();
}

// --- INITIALIZE EVENT LISTENERS ---
document.querySelectorAll('.toggle').forEach(btn => {
  btn.addEventListener('click', () => {
    state.view = btn.dataset.view;
    document.querySelectorAll('.toggle').forEach(b => b.classList.toggle('active', b === btn));
    renderGraph();
    highlightSelection();
  });
});

if (searchInput) {
  searchInput.addEventListener('input', e => {
    state.query = e.target.value;
    rerender();
  });
}

const themeBtn = document.querySelector('[data-theme-toggle]');
if (themeBtn) {
  themeBtn.addEventListener('click', () => {
    const root = document.documentElement;
    const next = root.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    root.setAttribute('data-theme', next);
    themeBtn.textContent = next === 'dark' ? '☼' : '☾';
  });
}

// --- RUN INITIAL RENDERS ---
renderStats();
rerender();

function updateGraphTransform() {
  const viewport = document.getElementById('graphViewport');
  if (viewport) {
    viewport.style.transform = `translate(${graphState.panX}px, ${graphState.panY}px) scale(${graphState.zoomScale})`;
  }
}

function initGraphZoom() {
  if (!graph) return;
  
  graph.addEventListener('mousedown', e => {
    if (e.target.closest('.node') || e.target.closest('.zoom-controls') || e.target.closest('.sidebar-toggle')) return;
    graphState.isDragging = true;
    graphState.startX = e.clientX - graphState.panX;
    graphState.startY = e.clientY - graphState.panY;
    graph.style.cursor = 'grabbing';
  });

  window.addEventListener('mousemove', e => {
    if (!graphState.isDragging) return;
    graphState.panX = e.clientX - graphState.startX;
    graphState.panY = e.clientY - graphState.startY;
    updateGraphTransform();
  });

  window.addEventListener('mouseup', () => {
    if (graphState.isDragging) {
      graphState.isDragging = false;
      if (graph) graph.style.cursor = 'grab';
    }
  });

  graph.addEventListener('wheel', e => {
    e.preventDefault();
    const zoomFactor = 1.1;
    const oldScale = graphState.zoomScale;
    
    const rect = graph.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;
    
    if (e.deltaY < 0) {
      graphState.zoomScale = Math.min(2.5, graphState.zoomScale * zoomFactor);
    } else {
      graphState.zoomScale = Math.max(0.4, graphState.zoomScale / zoomFactor);
    }
    
    graphState.panX = mouseX - (mouseX - graphState.panX) * (graphState.zoomScale / oldScale);
    graphState.panY = mouseY - (mouseY - graphState.panY) * (graphState.zoomScale / oldScale);
    
    updateGraphTransform();
  }, { passive: false });
  
  // Touch panning
  let lastTouchX = 0, lastTouchY = 0;
  graph.addEventListener('touchstart', e => {
    if (e.target.closest('.node') || e.target.closest('.zoom-controls') || e.target.closest('.sidebar-toggle')) return;
    if (e.touches.length === 1) {
      graphState.isDragging = true;
      lastTouchX = e.touches[0].clientX;
      lastTouchY = e.touches[0].clientY;
    }
  });

  graph.addEventListener('touchmove', e => {
    if (!graphState.isDragging) return;
    if (e.touches.length === 1) {
      const dx = e.touches[0].clientX - lastTouchX;
      const dy = e.touches[0].clientY - lastTouchY;
      graphState.panX += dx;
      graphState.panY += dy;
      lastTouchX = e.touches[0].clientX;
      lastTouchY = e.touches[0].clientY;
      updateGraphTransform();
    }
  });

  graph.addEventListener('touchend', () => {
    graphState.isDragging = false;
  });
  
  graph.style.cursor = 'grab';
}

// --- COLLAPSIBLE SIDEBAR CONTROLLER ---
const shell = document.querySelector('.shell');
const sidebarOverlay = document.getElementById('sidebarOverlay');
const collapseBtn = document.getElementById('sidebarCollapseBtn');
const expandBtn = document.getElementById('sidebarExpandBtn');

function setSidebarState(collapsed) {
  if (collapsed) {
    if (shell) shell.classList.add('sidebar-collapsed');
    if (expandBtn) expandBtn.style.display = 'grid';
    if (sidebarOverlay) sidebarOverlay.classList.remove('active');
  } else {
    if (shell) shell.classList.remove('sidebar-collapsed');
    if (expandBtn) expandBtn.style.display = 'none';
    if (sidebarOverlay && window.innerWidth <= 1080) {
      sidebarOverlay.classList.add('active');
    }
  }
}

if (collapseBtn) {
  collapseBtn.addEventListener('click', () => setSidebarState(true));
}
if (expandBtn) {
  expandBtn.addEventListener('click', () => setSidebarState(false));
}
if (sidebarOverlay) {
  sidebarOverlay.addEventListener('click', () => setSidebarState(true));
}

initGraphZoom();

// Collapse sidebar by default on mobile
if (window.innerWidth <= 1080) {
  setSidebarState(true);
}

