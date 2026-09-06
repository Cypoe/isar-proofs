"""
Basis boundary — re-exports the pure tower (L0/L1) for graph import.

See `tower.py` for stratification. Prefer `import tower` in new code.
"""
from __future__ import annotations

from tower import (  # noqa: F401
    derived_s,
    derived_k_signature,
    translate_to_basis,
    quote_s,
    quote_surface,
    layer_summary,
    op_norm,
    op_comp,
    op_dup,
    op_swap,
    op_app,
)
