# SPDX-License-Identifier: LGPL-3.0-or-later
"""Writes `verifier/src/Residual.sol`, whose table builds and lookups are unrolled."""

from pathlib import Path

M128 = "0xffffffffffffffffffffffffffffffff"
X_INV = "0x80000000000000000000000000000043"


def indent(block: str, n: int) -> str:
    return "\n".join((" " * n + line) if line else "" for line in block.split("\n"))


RED = f"""function red(v) -> o {{
    let h := shr(128, v)
    o := xor(and(v, {M128}), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
    h := shr(128, o)
    o := xor(and(o, {M128}), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
}}"""

TAB4 = """function tab4(x, t) {
    let x2 := shl(1, x)
    let x3 := xor(x2, x)
    let x4 := shl(2, x)
    let x8 := shl(3, x)
    let x12 := xor(x8, x4)
    mstore(t, 0)
    mstore(add(t, 0x20), x)
    mstore(add(t, 0x40), x2)
    mstore(add(t, 0x60), x3)
    mstore(add(t, 0x80), x4)
    mstore(add(t, 0xa0), xor(x4, x))
    mstore(add(t, 0xc0), xor(x4, x2))
    mstore(add(t, 0xe0), xor(x4, x3))
    mstore(add(t, 0x100), x8)
    mstore(add(t, 0x120), xor(x8, x))
    mstore(add(t, 0x140), xor(x8, x2))
    mstore(add(t, 0x160), xor(x8, x3))
    mstore(add(t, 0x180), x12)
    mstore(add(t, 0x1a0), xor(x12, x))
    mstore(add(t, 0x1c0), xor(x12, x2))
    mstore(add(t, 0x1e0), xor(x12, x3))
}"""


def scan() -> str:
    lines = ["function scan(t, y) -> o {", "    let n := byte(16, y)", "    o := xor(shl(4, mload(add(t, shl(5, shr(4, n))))), mload(add(t, shl(5, and(n, 15)))))"]
    for k in range(17, 32):
        lines.append(f"    n := byte({k}, y)")
        lines.append("    o := xor(xor(shl(8, o), shl(4, mload(add(t, shl(5, shr(4, n)))))), mload(add(t, shl(5, and(n, 15)))))")
    lines.append("}")
    return "\n".join(lines)


MUL256 = f"""function mul256(x, y, t) -> o {{
    let x0 := and(x, {M128})
    let x1 := shr(128, x)
    let y0 := and(y, {M128})
    let y1 := shr(128, y)
    tab4(x0, t)
    let p0 := scan(t, y0)
    tab4(x1, t)
    let p1 := scan(t, y1)
    tab4(xor(x0, x1), t)
    let p2 := scan(t, xor(y0, y1))
    o := or(shl(128, red(xor(p2, p0))), red(xor(xor(p0, shr(1, p1)), mul(and(p1, 1), {X_INV}))))
}}"""

BY128 = f"""function by128(x, t) -> o {{
    o := or(shl(128, red(scan(t, shr(128, x)))), red(scan(t, and(x, {M128}))))
}}"""

WK = """function wk(sub_, row, bits) -> o {
    for { let b := row } shr(b, bits) { b := add(b, 1) } {
        if and(shr(b, bits), 1) {
            o := xor(o, shr(128, mload(add(sub_, mul(16, add(mul(row, 32), b))))))
        }
    }
}"""


def look() -> str:
    lines = ["function look(tab, m) -> o {", "    o := xor(mload(add(tab, shl(5, byte(31, m)))), mload(add(tab, add(0x2000, shl(5, byte(30, m))))))"]
    for g in range(2, 16, 2):
        a = f"mload(add(tab, add({hex(g * 0x2000)}, shl(5, byte({31 - g}, m)))))"
        b = f"mload(add(tab, add({hex((g + 1) * 0x2000)}, shl(5, byte({30 - g}, m)))))"
        lines.append(f"    o := xor(o, xor({a}, {b}))")
    lines.append("}")
    return "\n".join(lines)


def hmul() -> str:
    lines = ["function hmul(h, y) -> o {", "    o := mload(add(h, shl(5, byte(16, y))))"]
    for k in range(17, 32):
        lines.append(f"    o := xor(shl(8, o), mload(add(h, shl(5, byte({k}, y)))))")
    lines.append("}")
    return "\n".join(lines)


HORNER = """function horner(h, a) {
    mstore(h, 0)
    for { let i := 1 } lt(i, 256) { i := add(i, 1) } {
        mstore(add(h, shl(5, i)), xor(shl(1, mload(add(h, shl(5, shr(1, i))))), mul(and(i, 1), a)))
    }
}"""

XTIME = f"""function xtime(v) -> o {{
    o := xor(and(shl(1, v), {M128}), mul(shr(127, v), 0x87))
}}"""

MASKS = f"""function masks(v, out) {{
    let rv := or(shl(1, and(v, 0x55555555555555555555555555555555)), and(shr(1, v), 0x55555555555555555555555555555555))
    rv := or(shl(2, and(rv, 0x33333333333333333333333333333333)), and(shr(2, rv), 0x33333333333333333333333333333333))
    rv := or(shl(4, and(rv, 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)), and(shr(4, rv), 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f))
    rv := or(shl(8, and(rv, 0x00ff00ff00ff00ff00ff00ff00ff00ff)), and(shr(8, rv), 0x00ff00ff00ff00ff00ff00ff00ff00ff))
    rv := or(shl(16, and(rv, 0x0000ffff0000ffff0000ffff0000ffff)), and(shr(16, rv), 0x0000ffff0000ffff0000ffff0000ffff))
    rv := or(shl(32, and(rv, 0x00000000ffffffff00000000ffffffff)), and(shr(32, rv), 0x00000000ffffffff00000000ffffffff))
    rv := or(shl(64, and(rv, 0xffffffffffffffff)), shr(64, rv))
    let low := and(rv, 0x7f)
    let m127 := xor(rv, xor(shl(121, low), xor(shl(126, and(low, 3)), shl(127, and(low, 1)))))
    let s := and(shl(1, m127), {M128})
    let prev := 0
    for {{ let k := 0 }} lt(k, 128) {{ k := add(k, 1) }} {{
        let m := xor(and(shl(1, prev), {M128}), and(shr(k, v), 1))
        if or(lt(k, 3), eq(k, 7)) {{ m := xor(m, s) }}
        mstore(add(out, shl(5, k)), m)
        prev := m
    }}
}}"""


def build_body() -> str:
    lines = [
        "mstore(b, 0)",
        "mstore(add(b, 0x20), mload(vg))",
    ]
    for i in range(2, 256):
        t = i.bit_length() - 1
        src = i - (1 << t)
        vt = f"v{t}" if t >= 4 else f"mload(add(vg, {hex(32 * t)}))"
        if src == 0:
            lines.append(f"mstore(add(b, {hex(32 * i)}), {vt})")
        else:
            lines.append(f"mstore(add(b, {hex(32 * i)}), xor(mload(add(b, {hex(32 * src)})), {vt}))")
    return "\n".join(lines)


def spread_row() -> str:
    lines = ["function spreadRow(base, sh, v, sp) {"]
    for g in range(16):
        slot = f"add(base, {hex(128 * g)})" if g else "base"
        lines.append(f"    mstore({slot}, xor(mload({slot}), shl(sh, mload(add(sp, shl(5, byte({31 - g}, v)))))))")
    lines.append("}")
    return "\n".join(lines)


def helpers(*names: str) -> str:
    table = {
        "red": RED,
        "tab4": TAB4,
        "scan": scan(),
        "mul256": MUL256,
        "by128": BY128,
        "wk": WK,
        "look": look(),
        "hmul": hmul(),
        "horner": HORNER,
        "xtime": XTIME,
        "masks": MASKS,
        "spreadRow": spread_row(),
    }
    return "\n".join(table[n] for n in names)


def asm(names: tuple[str, ...], body: str) -> str:
    return indent(helpers(*names) + "\n" + body.strip("\n"), 12)


TEMPLATE = Path(__file__).with_name("Residual.sol.in").read_text()
FIELD = ("red", "tab4", "scan", "mul256")
out = TEMPLATE
out = out.replace("        // @BUILD\n", indent(build_body(), 16) + "\n")
for marker, names in {
    "RANK": FIELD + ("look",),
    "STEP_B": ("red", "hmul", "horner", "look", "masks"),
    "POINT": FIELD + ("look", "xtime", "spreadRow"),
    "KERNEL": FIELD + ("by128", "wk"),
}.items():
    start = f"            // @{marker}\n"
    end = f"            // @END\n"
    a = out.index(start)
    b = out.index(end, a)
    out = out[:a] + asm(names, out[a + len(start) : b]) + "\n" + out[b + len(end) :]
Path(__file__).parent.parent.joinpath("src/Residual.sol").write_text(out)
