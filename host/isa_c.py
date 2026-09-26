"""
isa_c — C11 statements as data: the "instruction" layer for the C
target, in the same Program/label/i shape as isa_x86_64.

A C Program is a list of ("label", name) | ("i", form, *ops) items;
FN-form items open a function body, "end" closes any block.
encode(item) renders one item to source bytes; assemble(prog) emits
the whole indented text plus a label->byte-offset table — the same
two-stage contract the x86_64 assembler satisfies, with nominal
resolution (identifiers) instead of addresses.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Tuple


Program = List[Tuple]


def LBL(name: str) -> Tuple:
    return ("label", name)


def I(form: str, *ops) -> Tuple:
    return ("i", form, *ops)


def FN(ret: str, name: str, params: str = "void") -> Tuple:
    return ("i", "fn", ret, name, params)


# ----------------------------------------------------------------------
# per-item rendering — C statement vocabulary
# ----------------------------------------------------------------------
#
#   fn ret name params      ret name(params) {
#   end                     }                      (closes fn/if/while/for)
#   if cond                 if (cond) {
#   elif cond               } else if (cond) {
#   else                    } else {
#   while cond              while (cond) {
#   for init cond step      for (init; cond; step) {
#   decl ty name [init]     ty name;  |  ty name = init;
#   assign lhs rhs          lhs = rhs;
#   do expr                 expr;
#   ret [expr]              return;  |  return expr;
#   break / continue        break; / continue;
#   raw text...             verbatim line (escape hatch — greppable)
#   note text               /* text */


def encode(insn: Tuple, resolve=None) -> bytes:
    """Render one item (label or i-tuple) to unindented source bytes."""
    if insn[0] == "label":
        return f"{insn[1]}:".encode()
    form, ops = insn[1], insn[2:]
    if form == "fn":
        ret, name, params = ops
        return f"{ret} {name}({params}) {{".encode()
    if form == "end":
        return b"}"
    if form == "if":
        return f"if ({ops[0]}) {{".encode()
    if form == "elif":
        return f"}} else if ({ops[0]}) {{".encode()
    if form == "else":
        return b"} else {"
    if form == "while":
        return f"while ({ops[0]}) {{".encode()
    if form == "for":
        return f"for ({ops[0]}; {ops[1]}; {ops[2]}) {{".encode()
    if form == "decl":
        ty, name = ops[0], ops[1]
        init = f" = {ops[2]}" if len(ops) > 2 else ""
        return f"{ty} {name}{init};".encode()
    if form == "assign":
        return f"{ops[0]} = {ops[1]};".encode()
    if form == "do":
        return f"{ops[0]};".encode()
    if form == "ret":
        return f"return{f' {ops[0]}' if ops else ''};".encode()
    if form == "break":
        return b"break;"
    if form == "continue":
        return b"continue;"
    if form == "raw":
        return " ".join(str(o) for o in ops).encode()
    if form == "note":
        return f"/* {ops[0]} */".encode()
    raise ValueError(f"isa_c: unknown form {form!r}")


# forms that close a block / open a block / re-open at outer depth
_CLOSERS = {"end"}
_DEDENT = {"end", "elif", "else"}
_OPENERS = {"fn", "if", "elif", "else", "while", "for"}


def assemble(program: Program, symbols: Dict[str, int] = None,
             base: int = 0) -> Tuple[bytes, Dict[str, int]]:
    """Render a C Program to indented source text.

    `symbols`/`base` are accepted for the shared assembler contract;
    resolution in C is nominal (identifiers), so both are ignored.
    Returns (source_bytes, labels) where labels maps each label name
    to its byte offset in the emitted text — the same diagnostic
    table the binary assemblers return."""
    del symbols, base
    out = bytearray()
    labels: Dict[str, int] = {}
    depth = 0
    for item in program:
        line = encode(item)
        if item[0] == "label":
            labels[item[1]] = len(out)
            out += b"    " * max(depth - 1, 0) + line + b"\n"
            continue
        form = item[1]
        d = depth - 1 if form in _DEDENT else depth
        out += b"    " * max(d, 0) + line + b"\n"
        if form in _CLOSERS:
            depth -= 1
        elif form in _OPENERS and form not in _DEDENT:
            depth += 1
        elif form in ("elif", "else"):
            pass  # depth unchanged: closes and reopens one block
    return bytes(out), labels


def render(program: Program) -> str:
    """Source text view of a Program (ISA.render slot)."""
    return assemble(program)[0].decode()


@dataclass(frozen=True)
class ISA:
    name: str            # "c"
    bits: int            # 64 — kernel arithmetic is uint64_t
    insn: tuple          # form vocabulary
    fields: dict         # operand slot names per form
    templates: dict      # emitted-line templates per form
    encode: Callable     # encode(item, resolve=None) -> bytes
    assemble: Callable   # assemble(prog, symbols, base) -> (bytes, labels)
    render: Callable     # render(prog) -> str


FORMS: Tuple[str, ...] = (
    "fn", "end", "if", "elif", "else", "while", "for",
    "decl", "assign", "do", "ret", "break", "continue",
    "raw", "note",
)

FIELDS: Dict[str, Tuple[str, ...]] = {
    "fn": ("ret", "name", "params"),
    "if": ("cond",), "elif": ("cond",), "while": ("cond",),
    "for": ("init", "cond", "step"),
    "decl": ("ty", "name", "init"),
    "assign": ("lhs", "rhs"), "do": ("expr",), "ret": ("expr",),
    "raw": ("text",), "note": ("text",),
}

C_ISA = ISA(
    name="c",
    bits=64,
    insn=FORMS,
    fields=FIELDS,
    templates={},
    encode=encode,
    assemble=assemble,
    render=render,
)


def main() -> int:
    ok = True
    prog: Program = [
        ("i", "note", "isa_c smoke"),
        FN("int", "main", "void"),
        ("i", "decl", "unsigned long long", "x", "41"),
        ("i", "if", "x > 0"),
        ("i", "assign", "x", "x + 1"),
        ("i", "else"),
        ("i", "assign", "x", "0"),
        ("i", "end"),
        LBL("done"),
        ("i", "ret", "x"),
        ("i", "end"),
    ]
    text, labels = assemble(prog)
    src = text.decode()
    checks = [
        ("fn open", "int main(void) {" in src),
        ("decl", "    unsigned long long x = 41;" in src),
        ("if open", "    if (x > 0) {" in src),
        ("nested assign", "        x = x + 1;" in src),
        ("else dedent", "    } else {" in src),
        ("label", "done:" in src and "done" in labels),
        ("ret", "    return x;" in src),
        ("close", src.rstrip().endswith("}")),
    ]
    for name, good in checks:
        print(f"  {'ok' if good else 'FAIL'} {name}")
        ok = ok and good
    if not ok:
        print(src)
    print(f"{'OK' if ok else 'FAIL'} isa_c")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
