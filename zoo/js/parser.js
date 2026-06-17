// --- PROPOSITIONAL LOGIC AST PARSER ---
export function parseLogic(str) {
  const tokens = str.match(/[A-Z]+|&|\||~|=>|\(|\)/g) || [];
  let idx = 0;
  function parseImplies() {
    let node = parseOr();
    while (idx < tokens.length && tokens[idx] === '=>') {
      idx++;
      const right = parseOr();
      node = { type: 'implies', left: node, right };
    }
    return node;
  }
  function parseOr() {
    let node = parseAnd();
    while (idx < tokens.length && tokens[idx] === '|') {
      idx++;
      const right = parseAnd();
      node = { type: 'or', left: node, right };
    }
    return node;
  }
  function parseAnd() {
    let node = parsePrimary();
    while (idx < tokens.length && tokens[idx] === '&') {
      idx++;
      const right = parsePrimary();
      node = { type: 'and', left: node, right };
    }
    return node;
  }
  function parsePrimary() {
    if (idx >= tokens.length) throw new Error("Unexpected end of input");
    const tok = tokens[idx];
    if (tok === '~') {
      idx++;
      return { type: 'not', body: parsePrimary() };
    }
    if (tok === '(') {
      idx++;
      const node = parseImplies();
      if (tokens[idx] !== ')') throw new Error("Expected ')'");
      idx++;
      return node;
    }
    if (/[A-Z]+/.test(tok)) {
      idx++;
      return { type: 'var', name: tok };
    }
    throw new Error(`Unexpected token: ${tok}`);
  }
  return parseImplies();
}

// --- LAMBDA CALCULUS PARSER ---
export function parseLambda(str) {
  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const c = str[i];
    if (/\s/.test(c)) {
      i++;
    } else if (c === '\\' || c === 'λ') {
      tokens.push({ type: 'lambda' });
      i++;
    } else if (c === '.') {
      tokens.push({ type: 'dot' });
      i++;
    } else if (c === '(' || c === ')') {
      tokens.push({ type: c });
      i++;
    } else if (/[a-zA-Z0-9']/.test(c)) {
      let name = '';
      while (i < str.length && /[a-zA-Z0-9']/.test(str[i])) {
        name += str[i];
        i++;
      }
      tokens.push({ type: 'var', name });
    } else {
      throw new Error(`Unexpected character: ${c}`);
    }
  }

  let tokenIdx = 0;
  function peek() { return tokens[tokenIdx]; }
  function consume() { return tokens[tokenIdx++]; }

  function parseExpression() {
    let terms = [];
    while (tokenIdx < tokens.length) {
      const tok = peek();
      if (tok.type === ')') {
        break;
      }
      terms.push(parsePrimary());
    }
    if (terms.length === 0) throw new Error("Empty expression");
    let result = terms[0];
    for (let k = 1; k < terms.length; k++) {
      result = { type: 'app', left: result, right: terms[k] };
    }
    return result;
  }

  function parsePrimary() {
    const tok = peek();
    if (!tok) throw new Error("Unexpected end of input");
    if (tok.type === 'lambda') {
      consume(); // lambda
      const params = [];
      while (peek() && peek().type === 'var') {
        params.push(consume().name);
      }
      if (peek() && peek().type === 'dot') {
        consume(); // dot
      } else {
        throw new Error("Expected '.' after lambda parameters");
      }
      let body = parseExpression();
      for (let k = params.length - 1; k >= 0; k--) {
        body = { type: 'abs', param: params[k], body };
      }
      return body;
    } else if (tok.type === '(') {
      consume(); // '('
      const expr = parseExpression();
      if (!peek() || peek().type !== ')') {
        throw new Error("Expected ')'");
      }
      consume(); // ')'
      return expr;
    } else if (tok.type === 'var') {
      return consume();
    } else {
      throw new Error(`Unexpected token: ${tok.type}`);
    }
  }

  return parseExpression();
}

// --- COMBINATOR EXPRESSION PARSER ---
export function parseCombinatorExpr(str) {
  const knownNames = [
    "C'B", "K2", "K3", "K4", "S'", "B'", "C'",
    "ι", "I", "K", "S", "B", "C", "A", "U", "Z", "P", "R", "O", "J", "X", "Y"
  ];

  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const c = str[i];
    if (/\s/.test(c)) {
      i++;
      continue;
    }
    if (c === '(' || c === ')') {
      tokens.push(c);
      i++;
      continue;
    }

    let matched = false;
    for (let name of knownNames) {
      if (str.startsWith(name, i)) {
        tokens.push(name);
        i += name.length;
        matched = true;
        break;
      }
    }

    if (!matched) {
      if (/[a-zA-Z0-9]/.test(c)) {
        tokens.push(c);
        i++;
      } else {
        throw new Error(`Unexpected character: ${c}`);
      }
    }
  }

  let tokenIdx = 0;
  function parseExpr() {
    let terms = [];
    while (tokenIdx < tokens.length) {
      const tok = tokens[tokenIdx];
      if (tok === ')') break;
      if (tok === '(') {
        tokenIdx++;
        terms.push(parseExpr());
        if (tokens[tokenIdx] === ')') {
          tokenIdx++;
        } else {
          throw new Error("Missing ')'");
        }
      } else {
        tokenIdx++;
        terms.push({ type: 'leaf', name: tok });
      }
    }
    if (terms.length === 0) throw new Error("Empty expression");
    let result = terms[0];
    for (let k = 1; k < terms.length; k++) {
      result = { type: 'app', left: result, right: terms[k] };
    }
    return result;
  }

  return parseExpr();
}
