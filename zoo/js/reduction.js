// --- COMBINATOR REDUCTION ENGINE ---
export function getSpine(node) {
  const args = [];
  let curr = node;
  while (curr && curr.type === 'app') {
    args.unshift(curr.right);
    curr = curr.left;
  }
  return { head: curr, args };
}

export function cloneTerm(node) {
  if (!node) return null;
  if (node.type === 'leaf' || node.type === 'comb' || node.type === 'var') {
    return { type: node.type, name: node.name };
  }
  if (node.type === 'app') {
    return { type: 'app', left: cloneTerm(node.left), right: cloneTerm(node.right) };
  }
  return null;
}

export function reduceLMO(node) {
  if (!node) return { reduced: false, node: null };

  const spine = getSpine(node);
  if (spine.head && spine.head.type === 'leaf') {
    const name = spine.head.name;
    let arity = 0;
    if (name === 'ι') arity = 1;
    else if (name === 'I') arity = 1;
    else if (name === 'K') arity = 2;
    else if (name === 'S') arity = 3;
    else if (name === 'B') arity = 3;
    else if (name === 'C') arity = 3;
    else if (name === 'W') arity = 2;
    
    if (arity > 0 && spine.args.length >= arity) {
      let reducedTerm;
      const args = spine.args;
      if (name === 'ι') {
        reducedTerm = {
          type: 'app',
          left: { type: 'app', left: cloneTerm(args[0]), right: { type: 'leaf', name: 'S' } },
          right: { type: 'leaf', name: 'K' }
        };
      } else if (name === 'I') {
        reducedTerm = cloneTerm(args[0]);
      } else if (name === 'K') {
        reducedTerm = cloneTerm(args[0]);
      } else if (name === 'S') {
        const f = args[0], g = args[1], x = args[2];
        reducedTerm = {
          type: 'app',
          left: { type: 'app', left: cloneTerm(f), right: cloneTerm(x) },
          right: { type: 'app', left: cloneTerm(g), right: cloneTerm(x) }
        };
      } else if (name === 'B') {
        const f = args[0], g = args[1], x = args[2];
        reducedTerm = {
          type: 'app',
          left: cloneTerm(f),
          right: { type: 'app', left: cloneTerm(g), right: cloneTerm(x) }
        };
      } else if (name === 'C') {
        const f = args[0], x = args[1], y = args[2];
        reducedTerm = {
          type: 'app',
          left: { type: 'app', left: cloneTerm(f), right: cloneTerm(y) },
          right: cloneTerm(x)
        };
      } else if (name === 'W') {
        const f = args[0], x = args[1];
        reducedTerm = {
          type: 'app',
          left: { type: 'app', left: cloneTerm(f), right: cloneTerm(x) },
          right: cloneTerm(x)
        };
      }

      let result = reducedTerm;
      for (let k = arity; k < args.length; k++) {
        result = { type: 'app', left: result, right: cloneTerm(args[k]) };
      }
      return { reduced: true, node: result };
    }
  }

  if (node.type === 'app') {
    const leftRes = reduceLMO(node.left);
    if (leftRes.reduced) {
      return { reduced: true, node: { type: 'app', left: leftRes.node, right: node.right } };
    }
    const rightRes = reduceLMO(node.right);
    if (rightRes.reduced) {
      return { reduced: true, node: { type: 'app', left: node.left, right: rightRes.node } };
    }
  }

  return { reduced: false, node };
}

// --- PROPOSITIONAL LOGIC EVALUATOR ---
export function evalLogicNode(node, env) {
  if (node.type === 'var') return env[node.name] || false;
  if (node.type === 'not') return !evalLogicNode(node.body, env);
  if (node.type === 'and') return evalLogicNode(node.left, env) && evalLogicNode(node.right, env);
  if (node.type === 'or') return evalLogicNode(node.left, env) || evalLogicNode(node.right, env);
  if (node.type === 'implies') return !evalLogicNode(node.left, env) || evalLogicNode(node.right, env);
  return false;
}

// --- TURING MACHINE INCREMENTER STEP ---
export function stepTM(tape, head, state) {
  const symbol = tape[head] || 'B';
  let nextState = state;
  let writeSymbol = symbol;
  let move = 'R';
  
  if (state === 'q0') {
    if (symbol === '0' || symbol === '1') {
      nextState = 'q0';
      writeSymbol = symbol;
      move = 'R';
    } else if (symbol === 'B') {
      nextState = 'q1';
      writeSymbol = 'B';
      move = 'L';
    }
  } else if (state === 'q1') {
    if (symbol === '0') {
      nextState = 'q_halt';
      writeSymbol = '1';
      move = 'L';
    } else if (symbol === '1') {
      nextState = 'q1';
      writeSymbol = '0';
      move = 'L';
    } else if (symbol === 'B') {
      nextState = 'q_halt';
      writeSymbol = '1';
      move = 'L';
    }
  }
  
  const newTape = [...tape];
  if (head < 0) {
    newTape.unshift(writeSymbol);
    head = 0;
  } else if (head >= newTape.length) {
    newTape.push(writeSymbol);
  } else {
    newTape[head] = writeSymbol;
  }
  
  const nextHead = head + (move === 'R' ? 1 : -1);
  return { tape: newTape, head: nextHead, state: nextState, rule: `δ(${state}, ${symbol}) = (${nextState}, ${writeSymbol}, ${move})` };
}

// --- SEMI-THUE STRING REWRITING STEP ---
export function stepSRS(rulesStr, inputStr) {
  const rules = rulesStr.split('\n').map(line => {
    const parts = line.split('->').map(s => s.trim());
    if (parts.length === 2) return { lhs: parts[0], rhs: parts[1] };
    return null;
  }).filter(Boolean);

  for (let r of rules) {
    const idx = inputStr.indexOf(r.lhs);
    if (idx !== -1) {
      const output = inputStr.substring(0, idx) + r.rhs + inputStr.substring(idx + r.lhs.length);
      return { success: true, rule: `${r.lhs} → ${r.rhs}`, output };
    }
  }
  return { success: false, output: inputStr };
}
