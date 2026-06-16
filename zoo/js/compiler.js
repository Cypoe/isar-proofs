import { COMB_EXPANSIONS } from './data.js';
import { parseCombinatorExpr } from './parser.js';

// --- FREE VARIABLES ---
export function freeVars(term) {
  if (term.type === 'var') return new Set([term.name]);
  if (term.type === 'abs') {
    const s = freeVars(term.body);
    s.delete(term.param);
    return s;
  }
  if (term.type === 'app') {
    const s1 = freeVars(term.left);
    const s2 = freeVars(term.right);
    return new Set([...s1, ...s2]);
  }
  return new Set();
}

// --- LAMBDA TO SKI TRANSLATION ---
export function toSKI(term) {
  if (term.type === 'comb') {
    return { type: 'comb', name: term.name };
  }
  if (term.type === 'var') {
    return { type: 'var', name: term.name };
  }
  if (term.type === 'app') {
    return { type: 'app', left: toSKI(term.left), right: toSKI(term.right) };
  }
  if (term.type === 'abs') {
    const x = term.param;
    const body = term.body;
    // Rule 1: [x]x = I
    if (body.type === 'var' && body.name === x) {
      return { type: 'comb', name: 'I' };
    }
    // Eta contraction: [x](e x) = e (if x not free in e)
    if (body.type === 'app' && body.right.type === 'var' && body.right.name === x) {
      const fv = freeVars(body.left);
      if (!fv.has(x)) {
        return toSKI(body.left);
      }
    }
    // Rule 2: [x]e = K e (if x not free in e)
    const fv = freeVars(body);
    if (!fv.has(x)) {
      return { type: 'app', left: { type: 'comb', name: 'K' }, right: toSKI(body) };
    }
    // Rule 3: [x](e1 e2) = S ([x]e1) ([x]e2)
    if (body.type === 'app') {
      const e1 = { type: 'abs', param: x, body: body.left };
      const e2 = { type: 'abs', param: x, body: body.right };
      return {
        type: 'app',
        left: { type: 'app', left: { type: 'comb', name: 'S' }, right: toSKI(e1) },
        right: toSKI(e2)
      };
    }
    // Rule 4: [x](\y. e)
    if (body.type === 'abs') {
      const eliminated = toSKI(body);
      return toSKI({ type: 'abs', param: x, body: eliminated });
    }
  }
  throw new Error("Unknown term type in toSKI");
}

// --- EXPAND COMBINATORS TO IOTA TREE ---
export function expandToIota(node) {
  if (node.type === 'leaf' || node.type === 'comb' || node.type === 'var') {
    const name = node.name;
    if (name === 'ι' || !name) {
      return { left: null, right: null };
    }
    const expansion = COMB_EXPANSIONS[name];
    if (!expansion) {
      return { left: null, right: null };
    }
    const parsed = parseCombinatorExpr(expansion);
    return expandToIota(parsed);
  } else if (node.type === 'app') {
    return {
      left: expandToIota(node.left),
      right: expandToIota(node.right)
    };
  }
}

// --- FORMAT SKI TERM TO STRING ---
export function formatSKI(term) {
  if (!term) return '';
  if (term.type === 'comb' || term.type === 'var' || term.type === 'leaf') return term.name || '';
  if (term.type === 'app') {
    let left = formatSKI(term.left);
    let right = formatSKI(term.right);
    if (term.right && (
      term.right.type === 'app' ||
      (term.right.type === 'comb' && term.right.name && term.right.name.length > 1) ||
      (term.right.type === 'var' && term.right.name && term.right.name.length > 1) ||
      (term.right.type === 'leaf' && term.right.name && term.right.name.length > 1)
    )) {
      right = `(${right})`;
    }
    return `${left}${right}`;
  }
  return '';
}
