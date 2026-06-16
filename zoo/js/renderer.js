// --- CANVAS TREE DRAWING LOGIC ---

export function getTreeMaxDepth(node) {
  if (!node) return 0;
  if (node.left === null && node.right === null) return 1;
  return 1 + Math.max(getTreeMaxDepth(node.left), getTreeMaxDepth(node.right));
}

export function countSymbols(tree) {
  if (!tree) return 0;
  if (tree.left === null && tree.right === null) return 1;
  return countSymbols(tree.left) + countSymbols(tree.right) + 1;
}

export function getThemeColor(depth, maxDepth, theme) {
  const t = maxDepth > 0 ? depth / maxDepth : 0;
  if (theme === 'rainbow') {
    const hue = (t * 280) % 360;
    return `hsla(${hue}, 85%, 60%, 0.85)`;
  }
  if (theme === 'emerald') {
    const hue = 120 + t * 80;
    return `hsla(${hue}, 80%, 55%, 0.85)`;
  }
  if (theme === 'cyberpunk') {
    const hue = 300 - t * 120;
    return `hsla(${hue}, 90%, 65%, 0.85)`;
  }
  const light = 50 + t * 45;
  return `rgba(${Math.floor(light*2.55)}, ${Math.floor(light*2.55)}, ${Math.floor(light*2.55)}, 0.85)`;
}

export function drawTreeCanvas(canvas, iotaTree, state) {
  const ctx = canvas.getContext('2d');
  const w = canvas.width;
  const h = canvas.height;
  ctx.clearRect(0, 0, w, h);

  if (!iotaTree) return;

  const maxDepth = getTreeMaxDepth(iotaTree);

  if (state.layout === 'radial') {
    const initialLength = Math.min(w, h) * (0.22 + 0.13 * Math.min(1, 10 / maxDepth));
    const branchAngle = state.angle * Math.PI / 180;
    
    function drawRadial(node, x, y, angle, length, depth) {
      if (!node) return;
      
      const xChild = x + Math.cos(angle) * length;
      const yChild = y + Math.sin(angle) * length;
      
      ctx.beginPath();
      ctx.moveTo(x, y);
      ctx.lineTo(xChild, yChild);
      ctx.strokeStyle = getThemeColor(depth, maxDepth, state.theme);
      ctx.lineWidth = Math.max(0.5, 4.5 - (depth * 3.5 / maxDepth));
      ctx.stroke();
      
      if (node.left || node.right) {
        drawRadial(node.left, xChild, yChild, angle - branchAngle, length * state.scale, depth + 1);
        drawRadial(node.right, xChild, yChild, angle + branchAngle, length * state.scale, depth + 1);
      } else {
        ctx.beginPath();
        ctx.arc(xChild, yChild, Math.max(1.5, 4.5 - (depth * 3 / maxDepth)), 0, 2*Math.PI);
        ctx.fillStyle = getThemeColor(depth, maxDepth, state.theme);
        ctx.fill();
      }
    }
    drawRadial(iotaTree, w/2, h - 30, -Math.PI / 2, initialLength, 0);
    
  } else {
    function assignCoords(node, leftRange, rightRange, depth) {
      if (!node) return;
      const x = (leftRange + rightRange) / 2;
      const y = 35 + depth * ((h - 70) / Math.max(1, maxDepth - 1));
      node.x = x;
      node.y = y;
      assignCoords(node.left, leftRange, x, depth + 1);
      assignCoords(node.right, x, rightRange, depth + 1);
    }
    assignCoords(iotaTree, 30, w - 30, 0);
    
    function drawConnections(node) {
      if (!node) return;
      ctx.strokeStyle = 'color-mix(in oklab, var(--color-text) 15%, transparent)';
      ctx.lineWidth = 1.2;
      
      if (node.left) {
        ctx.beginPath();
        ctx.moveTo(node.x, node.y);
        ctx.lineTo(node.left.x, node.left.y);
        ctx.stroke();
        drawConnections(node.left);
      }
      if (node.right) {
        ctx.beginPath();
        ctx.moveTo(node.x, node.y);
        ctx.lineTo(node.right.x, node.right.y);
        ctx.stroke();
        drawConnections(node.right);
      }
    }
    drawConnections(iotaTree);
    
    function drawNodes(node, depth) {
      if (!node) return;
      const isLeaf = (node.left === null && node.right === null);
      
      ctx.beginPath();
      ctx.arc(node.x, node.y, isLeaf ? 5 : 3, 0, 2*Math.PI);
      ctx.fillStyle = isLeaf ? getThemeColor(depth, maxDepth, state.theme) : '#888';
      ctx.fill();
      
      if (isLeaf) {
        ctx.fillStyle = 'var(--color-text)';
        ctx.font = '10px Satoshi, sans-serif';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'top';
        ctx.fillText('ι', node.x, node.y + 6);
      }
      
      drawNodes(node.left, depth + 1);
      drawNodes(node.right, depth + 1);
    }
    drawNodes(iotaTree, 0);
  }
}
