"""Shared helpers for the nanopass gate suites."""

import os
import sys

_HOST = os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))
sys.path.insert(0, _HOST)
sys.path.insert(0, os.path.join(_HOST, "..", "seed"))

import seed                                                    # noqa: E402


_PROG_AXES = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
             "node_bytes", "stack_reserve", "peephole"}


def _fixed_of(R) -> dict:
    """emit_image's generation-pin rule: every non-λ Realization
    field pins at generation time."""
    return {k: getattr(R, k) for k in vars(seed.Realization())
            if k not in _PROG_AXES}

