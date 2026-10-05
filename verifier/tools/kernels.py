# SPDX-License-Identifier: LGPL-3.0-or-later
"""Writes `verifier/src/wrap/K.sol`: the wrap verifier's hot loops in assembly, each with the field
product inlined and, where a loop sums products, one reduction for the whole sum."""

from pathlib import Path

R = [sum(1 << q for q in range(256) if q % 5 == r) for r in range(5)]
M = [x & ((1 << 128) - 1) for x in R]
M128 = "0xffffffffffffffffffffffffffffffff"


def cl() -> str:
    """The product of two polynomials over GF(2) of degree below 128, unreduced."""
    lines = ["function cl(ka, kb) -> ko {"]
    for i in range(5):
        lines.append(f"    let a{i} := and(ka, 0x{M[i]:032x})")
    for i in range(5):
        lines.append(f"    let b{i} := and(kb, 0x{M[i]:032x})")
    for r in range(5):
        terms = [f"mul(a{i}, b{(r - i) % 5})" for i in range(5)]
        s = f"xor(xor({terms[0]}, {terms[1]}), xor(xor({terms[2]}, {terms[3]}), {terms[4]}))"
        masked = f"and({s}, 0x{R[r]:064x})"
        lines.append(f"    ko := {masked}" if r == 0 else f"    ko := xor(ko, {masked})")
    lines.append("}")
    return "\n".join(lines)


RED = f"""function red(kv) -> ko {{
    let h := shr(128, kv)
    ko := xor(and(kv, {M128}), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
    h := shr(128, ko)
    ko := xor(and(ko, {M128}), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
}}"""

MUL = """function gm(ka, kb) -> ko {
    ko := red(cl(ka, kb))
}"""

SQ = """function sq(ka) -> ko {
    ko := and(or(ka, shl(64, ka)), 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff)
    ko := and(or(ko, shl(32, ko)), 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff)
    ko := and(or(ko, shl(16, ko)), 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)
    ko := and(or(ko, shl(8, ko)), 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)
    ko := and(or(ko, shl(4, ko)), 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
    ko := and(or(ko, shl(2, ko)), 0x3333333333333333333333333333333333333333333333333333333333333333)
    ko := and(or(ko, shl(1, ko)), 0x5555555555555555555555555555555555555555555555555555555555555555)
    ko := red(ko)
}"""

# An extension element is `c1 << 128 | c0` with `u^2 = u + x^-1`.
MUL256 = f"""function xinv(kz) -> ko {{
    ko := xor(shr(1, kz), mul(and(kz, 1), 0x80000000000000000000000000000043))
}}
function gm2(ka, kb) -> ko {{
    let a0 := and(ka, {M128})
    let a1 := shr(128, ka)
    let b0 := and(kb, {M128})
    let b1 := shr(128, kb)
    let p0 := cl(a0, b0)
    let p1 := red(cl(a1, b1))
    let p2 := cl(xor(a0, a1), xor(b0, b1))
    ko := or(shl(128, red(xor(p2, p0))), xor(red(p0), xinv(p1)))
}}
function gm21(ka, ks) -> ko {{
    ko := or(shl(128, red(cl(shr(128, ka), ks))), red(cl(and(ka, {M128}), ks)))
}}"""


def indent(block: str, n: int) -> str:
    return "\n".join((" " * n + line) if line else "" for line in block.split("\n"))


def kernel(doc: str, signature: str, helpers: list[str], body: str, mutability: str = "pure") -> str:
    code = "\n".join(helpers) + "\n" + body
    doc_lines = "\n".join(f"    /// {line}" for line in doc.split("\n"))
    name, _, returns = signature.partition(" returns ")
    tail = f" returns {returns}" if returns else ""
    return f"""{doc_lines}
    function {name} internal {mutability}{tail} {{
        assembly ("memory-safe") {{
{indent(code, 12)}
        }}
    }}
"""


BASE = [cl(), RED]
KERNELS = []

KERNELS.append(kernel(
    "`Σ_i a[i]·b[i]` over the `n` words at memory `a` and at memory `b`.",
    "dot(uint256 a, uint256 b, uint256 n) returns (uint256 r)",
    BASE,
    """let acc := 0
for { let end := add(a, shl(5, n)) } lt(a, end) { a := add(a, 0x20) b := add(b, 0x20) } {
    acc := xor(acc, cl(mload(a), mload(b)))
}
r := red(acc)""",
))

KERNELS.append(kernel(
    "`Σ_i a[i]·v_i` over the `n` words at memory `a` and the `n` sixteen-byte values at calldata `at`.",
    "dotCalldata(uint256 a, uint256 at, uint256 n) returns (uint256 r)",
    BASE,
    """let acc := 0
for { let end := add(a, shl(5, n)) } lt(a, end) { a := add(a, 0x20) at := add(at, 16) } {
    acc := xor(acc, cl(mload(a), shr(128, calldataload(at))))
}
r := red(acc)""",
))

KERNELS.append(kernel(
    "Writes at memory `t` the equality table of the `n` coordinates at memory `point`, lowest\ncoordinate at the lowest index bit, scaled by `seed`: `2^n` words.",
    "eqTable(uint256 t, uint256 point, uint256 n, uint256 seed)",
    BASE + [MUL],
    """mstore(t, seed)
for { let j := 0 } lt(j, n) { j := add(j, 1) } {
    let x := mload(add(point, shl(5, j)))
    let half := shl(add(j, 5), 1)
    for { let p := t let end := add(t, half) } lt(p, end) { p := add(p, 0x20) } {
        let lo := mload(p)
        let hi := gm(lo, x)
        mstore(add(p, half), hi)
        mstore(p, xor(lo, hi))
    }
}""",
))

KERNELS.append(kernel(
    "Binds the lowest variable of the `2·half` words at memory `v` to `r`, in place:\n`v[k] ← v[2k] + r·(v[2k] + v[2k+1])`.",
    "fold(uint256 v, uint256 half, uint256 r)",
    BASE + [MUL],
    """for { let k := 0 } lt(k, half) { k := add(k, 1) } {
    let src := add(v, shl(6, k))
    let lo := mload(src)
    mstore(add(v, shl(5, k)), xor(lo, gm(r, xor(lo, mload(add(src, 0x20))))))
}""",
))

KERNELS.append(kernel(
    "`Π_i (1 + a[i] + b[i])` over the `n` words at memory `a` and at memory `b`.",
    "eqProduct(uint256 a, uint256 b, uint256 n) returns (uint256 r)",
    BASE + [MUL],
    """r := 1
for { let end := add(a, shl(5, n)) } lt(a, end) { a := add(a, 0x20) b := add(b, 0x20) } {
    r := gm(r, xor(1, xor(mload(a), mload(b))))
}""",
))

KERNELS.append(kernel(
    "`a^(2^k)`.",
    "frob(uint256 a, uint256 k) returns (uint256 r)",
    [RED, SQ],
    """r := a
for { } gt(k, 0) { k := sub(k, 1) } {
    r := sq(r)
}""",
))

KERNELS.append(kernel(
    "The value at `r` of a sumcheck round polynomial of degree `degree` from its message at\ncalldata `at`, every coefficient but the linear one, under the running claim `claim`.",
    "roundEval(uint256 at, uint256 degree, uint256 r, uint256 claim) returns (uint256 out)",
    BASE + [MUL],
    """let linear := claim
let acc := 0
for { let k := sub(degree, 1) } gt(k, 0) { k := sub(k, 1) } {
    let c := shr(128, calldataload(add(at, shl(4, k))))
    linear := xor(linear, c)
    acc := xor(gm(acc, r), c)
}
out := xor(gm(xor(gm(acc, r), linear), r), shr(128, calldataload(at)))""",
))

KERNELS.append(kernel(
    "Product of two extension elements.",
    "mul256(uint256 a, uint256 b) returns (uint256 r)",
    BASE + [MUL256],
    "r := gm2(a, b)",
))

KERNELS.append(kernel(
    "`acc·Π_i (1 + z[i] + y[i])` over the `n` extension words at memory `z` and at memory `y`.",
    "eqProduct256(uint256 acc, uint256 z, uint256 y, uint256 n) returns (uint256 r)",
    BASE + [MUL256],
    """r := acc
for { let end := add(z, shl(5, n)) } lt(z, end) { z := add(z, 0x20) y := add(y, 0x20) } {
    r := gm2(r, xor(1, xor(mload(z), mload(y))))
}""",
))

KERNELS.append(kernel(
    "Writes at memory `t` the equality table of the `n` extension coordinates at memory `point`:\n`2^n` words.",
    "eqTable256(uint256 t, uint256 point, uint256 n)",
    BASE + [MUL256],
    """mstore(t, 1)
for { let j := 0 } lt(j, n) { j := add(j, 1) } {
    let x := mload(add(point, shl(5, j)))
    let half := shl(add(j, 5), 1)
    for { let p := t let end := add(t, half) } lt(p, end) { p := add(p, 0x20) } {
        let lo := mload(p)
        let hi := gm2(lo, x)
        mstore(add(p, half), hi)
        mstore(p, xor(lo, hi))
    }
}""",
))

KERNELS.append(kernel(
    "`Σ_l e[l]·row_l` over the `lanes` extension words at memory `e` and a codeword row at\ncalldata `at`: sixteen-byte base values when `base` is set, else extension values stored low\ncoordinate first.",
    "rowFold(uint256 e, uint256 at, uint256 lanes, bool base) returns (uint256 r)",
    BASE + [MUL256],
    f"""switch base
case 1 {{
    let lo := 0
    let hi := 0
    for {{ let end := add(e, shl(5, lanes)) }} lt(e, end) {{ e := add(e, 0x20) at := add(at, 16) }} {{
        let w := mload(e)
        let v := shr(128, calldataload(at))
        lo := xor(lo, cl(and(w, {M128}), v))
        hi := xor(hi, cl(shr(128, w), v))
    }}
    r := or(shl(128, red(hi)), red(lo))
}}
default {{
    // Σ (e0 + e1·u)(r0 + r1·u) with u² = u + x^-1, from three sums of products reduced once each.
    let s0 := 0
    let s1 := 0
    let s2 := 0
    for {{ let end := add(e, shl(5, lanes)) }} lt(e, end) {{ e := add(e, 0x20) at := add(at, 32) }} {{
        let w := mload(e)
        let v := calldataload(at)
        let e0 := and(w, {M128})
        let e1 := shr(128, w)
        let r0 := shr(128, v)
        let r1 := and(v, {M128})
        s0 := xor(s0, cl(e0, r0))
        s1 := xor(s1, cl(e1, r1))
        s2 := xor(s2, cl(xor(e0, e1), xor(r0, r1)))
    }}
    r := or(shl(128, red(xor(s2, s0))), xor(red(s0), xinv(red(s1))))
}}""",
))

KERNELS.append(kernel(
    "`claim + e1 + (claim + einf + einf·r)·r` over the extension field: a sumcheck claim past the\nmessage `(e1, einf)` at challenge `r`.",
    "nextClaim256(uint256 claim, uint256 e1, uint256 einf, uint256 r) returns (uint256 out)",
    BASE + [MUL256],
    "out := xor(xor(claim, e1), gm2(xor(xor(claim, einf), gm2(einf, r)), r))",
))

KERNELS.append(kernel(
    "`Σ_{i<64} skip[i]·(lo_i + x0·(lo_i + hi_i))` for the 64 words at memory `skip` and the 128\nsixteen-byte values at calldata `at`, `lo` then `hi`.",
    "sliceCheck(uint256 skip, uint256 x0, uint256 at) returns (uint256 r)",
    BASE + [MUL],
    """let a := 0
let d := 0
for { let i := 0 } lt(i, 64) { i := add(i, 1) } {
    let w := mload(add(skip, shl(5, i)))
    let lo := shr(128, calldataload(add(at, shl(4, i))))
    let hi := shr(128, calldataload(add(at, shl(4, add(i, 64)))))
    a := xor(a, cl(w, lo))
    d := xor(d, cl(w, xor(lo, hi)))
}
r := xor(red(a), gm(x0, red(d)))""",
))

KERNELS.append(kernel(
    "`Σ_i gamma^i·v_i` over the `n` sixteen-byte values at calldata `at`.",
    "horner(uint256 at, uint256 n, uint256 gamma) returns (uint256 r)",
    BASE + [MUL],
    """for { let i := n } gt(i, 0) { i := sub(i, 1) } {
    r := xor(gm(r, gamma), shr(128, calldataload(add(at, shl(4, sub(i, 1))))))
}""",
))

KERNELS.append(kernel(
    "`Σ_j gamma^j·eq(rho^(2^-j), x)` over the 128 inverse Frobenius powers of the `n` coordinates at\nmemory `rho`, for the `n` coordinates at memory `x`, which it overwrites.",
    "twistedEq(uint256 gamma, uint256 rho, uint256 x, uint256 n) returns (uint256 acc)",
    BASE + [MUL, SQ],
    """let g := gamma
let e := 1
let end := add(x, shl(5, n))
for { let j := 0 } lt(j, 128) { j := add(j, 1) } {
    if j {
        for { let p := x } lt(p, end) { p := add(p, 0x20) } {
            mstore(p, sq(mload(p)))
        }
        g := sq(g)
        e := gm(sq(e), g)
    }
    let prod := e
    for { let p := x let q := rho } lt(p, end) { p := add(p, 0x20) q := add(q, 0x20) } {
        prod := gm(prod, xor(1, xor(mload(q), mload(p))))
    }
    acc := xor(sq(acc), prod)
}
acc := sq(acc)""",
))

KERNELS.append(kernel(
    "Writes at memory `out`, per run of the `count` twelve-byte records at memory `runs`, the product\nof the six table entries its two cumulative heights select: `tables` holds six pointers, three\nfor the first height's bytes and three for the second's.",
    "atRuns(uint256 out, uint256 runs, uint256 count, uint256 tables)",
    BASE + [MUL],
    """for { let i := 0 } lt(i, count) { i := add(i, 1) } {
    let rec := mload(add(runs, mul(i, 12)))
    let v := 0
    for { let h := 0 } lt(h, 2) { h := add(h, 1) } {
        // A height's low byte, middle byte and the rest, each into its table.
        let t := and(shr(sub(224, shl(5, h)), rec), 0xffffffff)
        let tp := add(tables, mul(h, 0x60))
        let w := gm(gm(mload(add(mload(tp), shl(5, and(t, 255)))), mload(add(mload(add(tp, 0x20)), shl(5, and(shr(8, t), 255))))), mload(add(mload(add(tp, 0x40)), shl(5, shr(16, t)))))
        switch h
        case 0 { v := w }
        default { v := gm(v, w) }
    }
    mstore(add(out, shl(5, i)), v)
}""",
))

KERNELS.append(kernel(
    "`Σ_runs at[run]·Σ_{columns of the run} table[column − base]` over the `count` twelve-byte run\nrecords at memory `runs`, the `len` words at memory `table` standing for the columns from `base`\nand every other column for zero.",
    "weigh(uint256 table, uint256 base, uint256 len, uint256 runs, uint256 count, uint256 at) returns (uint256 r)",
    BASE,
    """let acc := 0
let end := add(base, len)
for { let i := 0 } lt(i, count) { i := add(i, 1) } {
    let rec := mload(add(runs, mul(i, 12)))
    let start := and(shr(176, rec), 0xffff)
    let last := add(start, and(shr(160, rec), 0xffff))
    if or(iszero(gt(last, base)), iszero(lt(start, end))) { continue }
    if lt(start, base) { start := base }
    if gt(last, end) { last := end }
    let sum := 0
    for { let p := add(table, shl(5, sub(start, base))) let q := add(table, shl(5, sub(last, base))) } lt(p, q) { p := add(p, 0x20) } {
        sum := xor(sum, mload(p))
    }
    acc := xor(acc, cl(sum, mload(add(at, shl(5, i)))))
}
r := red(acc)""",
))

KERNELS.append(kernel(
    "Runs the layout's branching program down the layers `to .. from` at the coordinates at memory\n`sigma`, two per layer, over the four words of state at memory `g`, for the `nu` row coordinates\nat memory `row` and the `m` dense-index coordinates at memory `index`, both zero beyond their\nlengths. The program reads, per layer, a bit of the row, of the dense index and of each of a\ncolumn's two cumulative heights, carrying the sum of row and first height into the dense index\nand comparing the dense index with the second height; a state is the carry and whether the\nindex is below the height so far, at `0x40·carry + 0x20·below`, and the program starts from\nthe state `(0, 1, 0, 0)` above the top layer and ends in the first word.",
    "boundary(uint256 row, uint256 nu, uint256 index, uint256 m, uint256 sigma, uint256 from, uint256 to, uint256 g)",
    BASE + [MUL],
    """// Scratch: h[carry][bit][below] at 0x80·carry + 0x40·bit + 0x20·below.
let hs := mload(0x40)
for { let layer := from } gt(layer, to) { layer := sub(layer, 1) } {
    let l := sub(layer, 1)
    {
        // Per next carry: the index bit 0 or 1 against the height's bit, keeping or setting the comparison.
        let b0 := 1
        if lt(l, m) { b0 := xor(1, mload(add(index, shl(5, l)))) }
        let d := mload(add(sigma, add(shl(6, l), 0x20)))
        for { let k := 0 } lt(k, 2) { k := add(k, 1) } {
            let gp := add(g, shl(6, k))
            let hp := add(hs, shl(7, k))
            let g0 := mload(gp)
            let g1 := mload(add(gp, 0x20))
            let s := xor(g0, gm(d, xor(g0, g1)))
            let t := gm(b0, s)
            mstore(hp, t)
            mstore(add(hp, 0x60), xor(s, t))
            mstore(add(hp, 0x20), gm(b0, g1))
            mstore(add(hp, 0x40), xor(g0, gm(b0, g0)))
        }
    }
    {
        // The row bit and the first height's bit: both zero, exactly one, both one.
        let c := mload(add(sigma, shl(6, l)))
        switch lt(l, nu)
        case 0 {
            // No row bit: neither is one with weight 1 + c, exactly one with weight c.
            for { let k := 0 } lt(k, 4) { k := add(k, 1) } {
                let hp := add(hs, shl(5, k))
                let h0 := mload(hp)
                mstore(add(g, shl(5, k)), xor(h0, gm(c, xor(h0, mload(add(hp, 0x40))))))
            }
        }
        default {
            let a := mload(add(row, shl(5, l)))
            let both := gm(a, c)
            let none := xor(xor(1, a), xor(c, both))
            let one := xor(a, c)
            for { let k := 0 } lt(k, 4) { k := add(k, 1) } {
                // The state (carry, below) = (k >> 1, k & 1) reads h at 0x40·carry + 0x20·below onwards.
                let hp := add(hs, shl(5, k))
                mstore(add(g, shl(5, k)), xor(xor(gm(none, mload(hp)), gm(one, mload(add(hp, 0x40)))), gm(both, mload(add(hp, 0x80)))))
            }
        }
    }
}""",
))

KERNELS.append(kernel(
    "Adds the `n` words at memory `src` to those at memory `dst`.",
    "addInto(uint256 dst, uint256 src, uint256 n)",
    [],
    """for { let end := add(src, shl(5, n)) } lt(src, end) { src := add(src, 0x20) dst := add(dst, 0x20) } {
    mstore(dst, xor(mload(dst), mload(src)))
}""",
))

KERNELS.append(kernel(
    "`Σ_i a[i]·b[index_i]` over the `n` words at memory `a` and the words at memory `b` that the\n`n` two-byte indices at memory `indices` select.",
    "dotIndexed(uint256 a, uint256 b, uint256 indices, uint256 n) returns (uint256 r)",
    BASE,
    """let acc := 0
for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    acc := xor(acc, cl(mload(add(a, shl(5, i))), mload(add(b, shl(5, shr(240, mload(add(indices, shl(1, i)))))))))
}
r := red(acc)""",
))

KERNELS.append(kernel(
    "Reads `n` sixteen-byte values at calldata `at` into words at memory `out`; returns whether each\nsquares to the word at the same index of memory `prev`.",
    "roots(uint256 out, uint256 at, uint256 prev, uint256 n) returns (bool ok)",
    [RED, SQ],
    """ok := 1
for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    let v := shr(128, calldataload(add(at, shl(4, i))))
    mstore(add(out, shl(5, i)), v)
    ok := and(ok, eq(sq(v), mload(add(prev, shl(5, i)))))
}""",
))

KERNELS.append(kernel(
    "Product of an extension element and a base element.",
    "mul256By128(uint256 a, uint256 b) returns (uint256 r)",
    BASE + [MUL256],
    "r := gm21(a, b)",
))

KERNELS.append(kernel(
    "Binds the lowest variable of the `2·half` extension words at memory `v` to the base element\n`c` of a monomial basis, in place: `v[k] ← v[2k] + c·v[2k+1]`.",
    "foldShift256(uint256 v, uint256 half, uint256 c)",
    BASE + [MUL256],
    """for { let k := 0 } lt(k, half) { k := add(k, 1) } {
    let src := add(v, shl(6, k))
    mstore(add(v, shl(5, k)), xor(mload(src), gm21(mload(add(src, 0x20)), c)))
}""",
))

KERNELS.append(kernel(
    "Binds the lowest variable of the `2·half` extension words at memory `v` to the extension\nelement `r`, in place: `v[k] ← v[2k] + r·(v[2k] + v[2k+1])`.",
    "fold256(uint256 v, uint256 half, uint256 r)",
    BASE + [MUL256],
    """for { let k := 0 } lt(k, half) { k := add(k, 1) } {
    let src := add(v, shl(6, k))
    let lo := mload(src)
    mstore(add(v, shl(5, k)), xor(lo, gm2(r, xor(lo, mload(add(src, 0x20))))))
}""",
))


def low_part() -> str:
    """The multilinear polynomial with the values `w_t` at the corners `t` of three coordinates,
    from the coordinates and their products, unreduced: constants of degree at most six."""
    w = [0b1000011, 0b100001, 0b10000, 0b1000, 0b100, 0b10, 0b1, 0]
    names = {1: "s0", 2: "s1", 4: "s2", 3: "m01", 5: "m02", 6: "m12", 7: "m012"}
    terms = [f"0x{w[0]:x}"]
    for subset in range(1, 8):
        c = 0
        for t in range(8):
            if t & subset == t:
                c ^= w[t]
        terms += [f"shl({b}, {names[subset]})" if b else names[subset] for b in range(7) if c >> b & 1]
    expr = terms[0]
    for t in terms[1:]:
        expr = f"xor({expr}, {t})"
    return expr


KERNELS.append(kernel(
    "`Σ_j c_j·v_j^(2^j)` for the coefficients `c_j` with `Σ_t bit_t(w)·gamma·eq(r, t) = Σ_j c_j·w^(2^j)`,\nover the 128 sixteen-byte values `v_j` at calldata `values`, as `gamma` times a chain of\nsquarings over `c_j^(2^-j)·v_j / gamma^(2^-j)`, which has the closed form of `c_0 / gamma` at the\n`2^j`-th roots of the seven coordinates at memory `r`: their `2^(128−j)`-th powers, met in the\norder repeated squaring gives them. `d0` is `(x^6 + 1)^-1`.",
    "rootedSum(uint256 gamma, uint256 r, uint256 values, uint256 d0) returns (uint256 acc)",
    BASE + [MUL, SQ],
    f"""// Scratch: the seven coordinates' current powers.
let s := mload(0x40)
mcopy(s, r, 0xe0)
let m01 := gm(mload(s), mload(add(s, 0x20)))
let m02 := gm(mload(s), mload(add(s, 0x40)))
let m12 := gm(mload(add(s, 0x20)), mload(add(s, 0x40)))
let m012 := gm(m01, mload(add(s, 0x40)))
let high := gm(gm(xor(1, mload(add(s, 0x60))), xor(1, mload(add(s, 0x80)))), gm(xor(1, mload(add(s, 0xa0))), xor(1, mload(add(s, 0xc0)))))
for {{ let level := 128 }} gt(level, 0) {{ level := sub(level, 1) }} {{
    // Π_i (s_i + (1 + s_i)·x^(2^i)) over the squared coordinates.
    let top := 1
    for {{ let i := 0 }} lt(i, 7) {{ i := add(i, 1) }} {{
        let si := sq(mload(add(s, shl(5, i))))
        mstore(add(s, shl(5, i)), si)
        top := gm(top, xor(si, red(shl(shl(i, 1), xor(1, si)))))
    }}
    m01 := sq(m01)
    m02 := sq(m02)
    m12 := sq(m12)
    m012 := sq(m012)
    high := sq(high)
    let low := 0
    {{
        let s0 := mload(s)
        let s1 := mload(add(s, 0x20))
        let s2 := mload(add(s, 0x40))
        low := gm(high, red({low_part()}))
    }}
    acc := xor(sq(acc), gm(gm(d0, xor(top, low)), shr(128, calldataload(add(values, shl(4, sub(level, 1)))))))
}}
acc := gm(gamma, acc)""",
))

INV = """function sqn(ka, kn) -> ko {
    ko := ka
    for { } kn { kn := sub(kn, 1) } { ko := sq(ko) }
}
function finv(ka) -> ko {
    let b3 := gm(sq(gm(sq(ka), ka)), ka)
    let b7 := gm(sq(gm(sqn(b3, 3), b3)), ka)
    let b15 := gm(sq(gm(sqn(b7, 7), b7)), ka)
    let b31 := gm(sq(gm(sqn(b15, 15), b15)), ka)
    let b63 := gm(sq(gm(sqn(b31, 31), b31)), ka)
    ko := sq(gm(sq(gm(sqn(b63, 63), b63)), ka))
}"""

KERNELS.append(kernel(
    "Writes at memory `out`, for the `m` extension challenges `y_i = y0 + y1·u` at memory `y`, the\nconstants that turn a factor `1 + y_i·w`, `w` in the base field, into `kappa_i·(u + t)` with\n`t = tau_i + beta_i·(1 + w)`: `m` words of `tau_i`, then of `beta_i`, then of `kappa_i`, where\n`N = y0² + y0·y1 + x^-1·y1²` is the norm, `beta = N/y1`, `tau = 1 + y0/y1 + beta` and\n`kappa = y·y1/N`. Returns whether every `y1` and norm is invertible.",
    "shiftConstants(uint256 out, uint256 y, uint256 m) returns (bool ok)",
    BASE + [MUL, SQ, MUL256, INV],
    f"""// Scratch: per challenge, `y1` and the norm, then the products of everything before each.
let s := mload(0x40)
let pre := add(s, shl(6, m))
let acc := 1
for {{ let i := 0 }} lt(i, m) {{ i := add(i, 1) }} {{
    let w := mload(add(y, shl(5, i)))
    let y0 := and(w, {M128})
    let y1 := shr(128, w)
    let norm := xor(xor(sq(y0), gm(y0, y1)), xinv(sq(y1)))
    mstore(add(s, shl(6, i)), y1)
    mstore(add(s, add(shl(6, i), 0x20)), norm)
    mstore(add(pre, shl(6, i)), acc)
    acc := gm(acc, y1)
    mstore(add(pre, add(shl(6, i), 0x20)), acc)
    acc := gm(acc, norm)
}}
ok := iszero(iszero(acc))
acc := finv(acc)
for {{ let j := m }} gt(j, 0) {{ j := sub(j, 1) }} {{
    let i := sub(j, 1)
    let norm := mload(add(s, add(shl(6, i), 0x20)))
    let normInv := gm(acc, mload(add(pre, add(shl(6, i), 0x20))))
    acc := gm(acc, norm)
    let y1 := mload(add(s, shl(6, i)))
    let y1Inv := gm(acc, mload(add(pre, shl(6, i))))
    acc := gm(acc, y1)
    let w := mload(add(y, shl(5, i)))
    let beta := gm(norm, y1Inv)
    mstore(add(out, shl(5, i)), xor(xor(1, gm(and(w, {M128}), y1Inv)), beta))
    mstore(add(out, shl(5, add(m, i))), beta)
    mstore(add(out, shl(5, add(shl(1, m), i))), gm21(w, gm(y1, normInv)))
}}""",
))

KERNELS.append(kernel(
    "Writes at memory `nt` the windowed sums of the products `beta_i·Ŵ_i(x^j)`: for the variable `i`\nin `0..vars` and the window `k` in `0..windows` of four bits of a position, sixteen words at\n`16·(i·windows + k)`, entry `v` the sum over the bits `b` of `v` of the product at `j = 4k + b`,\nwhich is zero below `i` and from `logDomain` on. `beta` holds the variables' constants and\n`space` the subspace polynomials' sixteen-byte values at `32·i + j`.",
    "shiftWindows(uint256 nt, uint256 beta, uint256 space, uint256 vars, uint256 logDomain, uint256 windows)",
    BASE + [MUL],
    """for { let i := 0 } lt(i, vars) { i := add(i, 1) } {
    for { let k := 0 } lt(k, windows) { k := add(k, 1) } {
        let base := add(nt, shl(9, add(mul(i, windows), k)))
        mstore(base, 0)
        for { let b := 0 } lt(b, 4) { b := add(b, 1) } {
            let val := 0
            {
                let j := add(shl(2, k), b)
                if and(iszero(lt(j, i)), lt(j, logDomain)) {
                    val := mload(add(beta, shl(5, i)))
                    if gt(j, i) { val := gm(val, shr(128, mload(add(space, shl(4, add(shl(5, i), j)))))) }
                }
            }
            let half := shl(add(b, 5), 1)
            for { let p := base let end := add(base, half) } lt(p, end) { p := add(p, 0x20) } {
                mstore(add(p, half), xor(mload(p), val))
            }
        }
    }
}""",
))

KERNELS.append(kernel(
    "`coeff·Π_i (u + tau_i + Σ_{j ≥ i, bit j of pos} beta_i·Ŵ_i(x^j))` over `vars` variables, from the\n`vars` words at memory `tau` and the windowed sums `shiftWindows` wrote at memory `nt`.",
    "shiftProduct(uint256 coeff, uint256 pos, uint256 tau, uint256 nt, uint256 vars, uint256 windows) returns (uint256 r)",
    BASE + [MUL256],
    f"""r := coeff
for {{ let i := 0 }} lt(i, vars) {{ i := add(i, 1) }} {{
    let t := mload(add(tau, shl(5, i)))
    for {{ let k := shr(2, i) }} lt(k, windows) {{ k := add(k, 1) }} {{
        t := xor(t, mload(add(nt, shl(5, add(shl(4, add(mul(i, windows), k)), and(shr(shl(2, k), pos), 15))))))
    }}
    // (a0 + a1·u)·(u + t) with u² = u + x^-1.
    let a0 := and(r, {M128})
    let a1 := shr(128, r)
    r := or(shl(128, xor(xor(a0, a1), red(cl(a1, t)))), xor(red(cl(a0, t)), xinv(a1)))
}}""",
))


KERNELS.append(kernel(
    "`Σ_i a[i]·v_i` over the `n` words at memory `a` and the `n` sixteen-byte values at memory `at`.",
    "dotPacked(uint256 a, uint256 at, uint256 n) returns (uint256 r)",
    BASE,
    """let acc := 0
for { let end := add(a, shl(5, n)) } lt(a, end) { a := add(a, 0x20) at := add(at, 16) } {
    acc := xor(acc, cl(mload(a), shr(128, mload(at))))
}
r := red(acc)""",
))

HEADER = """// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

// Generated by `python3 verifier/tools/kernels.py`; do not edit.

/// The wrap verifier's hot loops over GF(2^128) and GF(2^256), in assembly: the field product is
/// inlined, and a loop that sums products reduces once, at the end. Elements are held as in `F`.
library K {
"""

if __name__ == "__main__":
    out = Path(__file__).resolve().parent.parent / "src" / "wrap" / "K.sol"
    out.write_text(HEADER + "\n".join(KERNELS) + "}\n")
