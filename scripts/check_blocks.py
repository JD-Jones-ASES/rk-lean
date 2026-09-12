#!/usr/bin/env python3
"""Independent checker for the two pools and the two exponent bounds.

Standard library only, Python >= 3.9.  Run it from anywhere:

    python scripts/check_blocks.py

What it checks, from the numbers alone:

1.  Every block of every pool is a ranked support: vertices are distinct residues below the
    modulus, the vertex 0 is present (the supports are normalised by translation), every rank is
    below the stated height, and along every arc -- every ordered pair of vertices whose
    difference is a nonzero k-th-power residue modulo m -- the rank strictly drops.  A ranking
    that strictly drops along every arc exists only for an acyclic digraph, so the blocks are
    acyclic; that is the whole point of the directed construction, and no separate acyclicity
    test is needed.  The set Q of nonzero k-th-power residues is recomputed here as the full
    image of z -> z^k mod m over all z < m, with 0 removed -- non-units included, exactly as in
    the formal definition.
2.  Every modulus is prime (hence square-free) and the moduli of a pool are pairwise coprime.
3.  The exponent alpha of each pool, recomputed to twelve decimal places in exact-context decimal
    arithmetic, and the two Ruzsa transfer values it is compared against.
4.  The rational bounds carried by RK/Numeric.lean: each is printed, each is re-checked as the
    exact natural-power comparison the Lean file discharges by `decide`, and the assembly
    (sum of the lower bounds) / (1 + k * sum of the upper bounds) is redone in exact rational
    arithmetic and compared against the decimal target and the transfer value.
5.  Controls that must fail: a block with one rank raised to equal its predecessor's, and a block
    with one vertex moved.  A checker that accepts these would be vacuous.

The pools below are the same numbers as `pool4` and `pool6` in `Challenge.lean`, and the rational
bounds are the same numbers as the `logLo`/`logHi` theorems of `RK/Numeric.lean`.  Nothing is read
from the Lean sources: the point of this script is to be a second, independent opinion.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
from math import gcd

getcontext().prec = 60

# ---------------------------------------------------------------------------
# The pools: the same numbers as `pool4` and `pool6` in `Challenge.lean`.
# Each block is (m, [(vertex, rank), ...], H).
# ---------------------------------------------------------------------------

POOL4 = [
    (5, [(0, 3), (1, 2), (2, 1), (3, 0)], 4),
    (13, [(0, 0), (2, 2), (5, 1), (7, 2), (8, 0), (10, 1), (12, 3)], 4),
    (29, [(0, 7), (1, 6), (2, 5), (3, 2), (5, 9), (6, 8), (14, 10), (15, 9), (16, 3), (17, 0),
          (25, 4), (26, 1)], 11),
    (37, [(0, 9), (3, 10), (5, 1), (8, 10), (10, 6), (13, 7), (15, 0), (18, 9), (20, 3), (23, 4),
          (26, 5), (32, 2), (34, 8)], 11),
    (53, [(0, 0), (3, 0), (5, 5), (6, 1), (8, 2), (11, 6), (14, 6), (17, 7), (29, 1), (32, 1),
          (35, 2), (37, 3), (38, 2), (40, 7), (41, 4), (43, 7)], 8),
    (61, [(0, 1), (4, 6), (7, 7), (14, 4), (17, 5), (24, 2), (27, 3), (31, 7), (35, 9), (37, 1),
          (41, 5), (45, 8), (47, 0), (51, 3), (55, 8), (57, 0)], 10),
    (101, [(0, 0), (3, 9), (6, 2), (10, 5), (11, 1), (13, 9), (14, 6), (15, 3), (17, 10), (18, 7),
           (21, 11), (28, 7), (29, 4), (32, 8), (57, 7), (61, 8), (69, 0), (72, 5), (75, 9),
           (76, 6)], 12),
    (109, [(0, 0), (2, 0), (4, 2), (12, 2), (34, 1), (36, 7), (42, 0), (44, 6), (46, 7), (52, 1),
           (54, 4), (62, 6), (71, 5), (76, 3), (84, 1), (86, 4), (88, 5), (94, 4), (95, 3),
           (101, 0), (103, 1)], 8),
]

POOL6 = [
    (7, [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)], 6),
    (19, [(0, 1), (2, 0), (4, 2), (5, 1), (6, 0), (8, 2), (10, 1), (11, 0), (14, 1), (15, 0)], 3),
    (31, [(0, 8), (2, 7), (4, 6), (6, 5), (7, 3), (9, 2), (11, 1), (13, 0), (16, 7), (18, 6),
          (20, 5), (22, 4), (24, 3), (26, 2), (28, 1)], 9),
    (43, [(0, 2), (2, 5), (3, 4), (6, 4), (7, 1), (12, 2), (13, 1), (16, 1), (17, 0), (19, 3),
          (22, 3), (23, 0), (25, 5), (26, 1), (31, 1), (36, 3), (37, 0), (40, 2)], 6),
    (67, [(0, 5), (2, 8), (4, 14), (5, 9), (6, 1), (10, 11), (11, 2), (14, 3), (16, 3), (18, 12),
          (24, 4), (25, 1), (27, 7), (32, 10), (34, 0), (36, 0), (42, 6), (44, 13), (53, 12),
          (55, 12), (63, 13), (64, 3), (65, 0)], 15),
    (79, [(0, 9), (2, 12), (5, 1), (7, 4), (8, 1), (14, 16), (19, 13), (20, 11), (22, 8), (24, 5),
          (25, 2), (30, 0), (36, 14), (37, 12), (39, 15), (42, 3), (44, 7), (45, 1), (49, 13),
          (56, 16), (58, 10), (61, 14), (62, 2), (65, 6), (67, 0), (74, 3), (78, 15)], 17),
    (103, [(0, 4), (2, 8), (4, 8), (7, 12), (8, 0), (11, 7), (13, 3), (15, 0), (18, 7), (19, 6),
           (20, 0), (25, 1), (30, 1), (35, 9), (36, 0), (40, 8), (47, 2), (51, 5), (52, 4),
           (57, 10), (62, 10), (63, 1), (67, 11), (68, 0), (78, 6), (83, 5), (85, 2), (88, 11),
           (90, 6), (95, 5)], 13),
    (127, [(0, 12), (2, 9), (6, 3), (9, 5), (19, 6), (21, 1), (24, 12), (26, 11), (28, 4), (32, 3),
           (43, 10), (45, 1), (47, 0), (50, 11), (52, 8), (58, 10), (62, 9), (65, 10), (69, 4),
           (71, 0), (81, 1), (84, 7), (86, 6), (88, 1), (91, 11), (93, 2), (98, 11), (99, 7),
           (100, 0), (107, 0), (110, 10), (114, 7), (122, 2)], 13),
    (139, [(0, 14), (6, 13), (7, 0), (18, 19), (24, 11), (25, 6), (27, 17), (31, 5), (33, 16),
           (38, 25), (39, 15), (42, 0), (44, 2), (47, 23), (49, 28), (54, 18), (58, 7), (66, 20),
           (67, 3), (74, 24), (79, 10), (85, 9), (91, 8), (93, 21), (96, 0), (104, 3), (110, 1),
           (117, 17), (118, 12), (120, 26), (126, 22), (128, 27), (135, 1), (137, 4)], 29),
]

POOLS = {4: POOL4, 6: POOL6}

# ---------------------------------------------------------------------------
# The rational bounds: the same numbers as the `logLo`/`logHi` theorems of RK/Numeric.lean.
# Keyed by modulus: (p, q) with p/q < log(m^(k-1) t)/log H, then (p, q) with log m/log H < p/q.
# ---------------------------------------------------------------------------

BOUNDS = {
    4: {5: ((1179, 263), (238, 205)),
        13: ((1370, 197), (420, 227)),
        29: ((1454, 277), (521, 371)),
        37: ((2017, 361), (128, 85)),
        53: ((346, 49), (758, 397)),
        61: ((2401, 366), (341, 191)),
        101: ((1735, 256), (743, 400)),
        109: ((2091, 254), (837, 371))},
    6: {7: ((1749, 272), (366, 337)),
        19: ((4587, 296), (729, 272)),
        31: ((3284, 363), (497, 318)),
        43: ((1889, 156), (254, 121)),
        67: ((2150, 241), (604, 389)),
        79: ((1837, 207), (566, 367)),
        103: ((1637, 158), (468, 259)),
        127: ((3123, 289), (17, 9)),
        139: ((2931, 350), (551, 376))},
}

# The decimal target of `alpha{k}_gt`, the rational core bound of `alpha{k}_gt_rational`, and the
# transfer value: r residues modulo `base`, so the exponent to exceed is (k - 1 + log r/log base)/k,
# bounded above using log r/log base < p/q (the `logHi_transfer` theorems).
TARGETS = {
    4: {"decimal": Fraction(9103, 10000), "core": Fraction(91033, 100000),
        "r": 6, "base": 17, "transfer_hi": (117, 185)},
    6: {"decimal": Fraction(9507, 10000), "core": Fraction(95071, 100000),
        "r": 6, "base": 13, "transfer_hi": (146, 209)},
}

# ---------------------------------------------------------------------------
# Bookkeeping
# ---------------------------------------------------------------------------

TOTAL = 0
FAILED = 0


def check(ok, what):
    """Count one check.  Prints only failures, plus a running total at the end."""
    global TOTAL, FAILED
    TOTAL += 1
    if not ok:
        FAILED += 1
        print("  FAILED: " + what)
    return ok


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def power_residues(k, m):
    """Q = the nonzero k-th-power residues mod m: the full image of z -> z^k, 0 removed."""
    return {pow(z, k, m) for z in range(m)} - {0}


def block_is_valid(k, m, sup, H):
    """`ValidRankedSupport k m sup H`, recomputed: the four conditions of the Lean definition,
    plus the normalisation `0 in S` which the pools satisfy (it is not part of the definition)."""
    vertices = [v for v, _ in sup]
    if len(set(vertices)) != len(vertices):
        return False, "vertices not distinct"
    if any(v >= m for v in vertices):
        return False, "a vertex is not below the modulus"
    if any(r >= H for _, r in sup):
        return False, "a rank is not below the height"
    Q = power_residues(k, m)
    rank = dict(sup)
    for x in vertices:
        for y in vertices:
            if x != y and (y - x) % m in Q and not rank[y] < rank[x]:
                return False, "no rank drop on the arc %d -> %d" % (x, y)
    if 0 not in vertices:
        return False, "the support is not normalised (0 is absent)"
    return True, "ok"


# ---------------------------------------------------------------------------
# 1-2.  The blocks, the moduli
# ---------------------------------------------------------------------------

print("Blocks, moduli")
for k in (4, 6):
    for (m, sup, H) in POOLS[k]:
        ok, why = block_is_valid(k, m, sup, H)
        check(ok, "k = %d, m = %d: %s" % (k, m, why))
        check(is_prime(m), "k = %d: modulus %d is prime (hence square-free)" % (k, m))
        check(H >= 2, "k = %d, m = %d: height at least 2" % (k, m))
        check(m >= 2, "k = %d, m = %d: modulus at least 2" % (k, m))
    moduli = [m for m, _, _ in POOLS[k]]
    for i in range(len(moduli)):
        for j in range(i + 1, len(moduli)):
            check(gcd(moduli[i], moduli[j]) == 1,
                  "k = %d: %d and %d coprime" % (k, moduli[i], moduli[j]))
    check(len(POOLS[k]) == (8 if k == 4 else 9), "k = %d: block count" % k)
    print("  k = %d: %d blocks, %d vertices in all, moduli %s"
          % (k, len(POOLS[k]), sum(len(s) for _, s, _ in POOLS[k]), moduli))

# ---------------------------------------------------------------------------
# 3.  The exponents and the transfer values, to twelve places
# ---------------------------------------------------------------------------

print()
print("Exponents")


def alpha_decimal(k):
    """alpha k P = (sum log(m^(k-1) t)/log H) / (1 + k sum log m/log H), in decimal arithmetic."""
    num = Decimal(0)
    den = Decimal(0)
    for (m, sup, H) in POOLS[k]:
        t = len(sup)
        num += (Decimal(m ** (k - 1) * t)).ln() / Decimal(H).ln()
        den += Decimal(m).ln() / Decimal(H).ln()
    return num / (1 + k * den)


for k in (4, 6):
    a = alpha_decimal(k)
    tgt = TARGETS[k]
    transfer = (Decimal(k - 1) + Decimal(tgt["r"]).ln() / Decimal(tgt["base"]).ln()) / Decimal(k)
    print("  alpha_%d      = %s" % (k, str(a.quantize(Decimal("1.000000000000")))))
    print("  transfer_%d   = %s  (%d residues mod %d)"
          % (k, str(transfer.quantize(Decimal("1.000000000000"))), tgt["r"], tgt["base"]))
    check(a > Decimal(tgt["decimal"].numerator) / Decimal(tgt["decimal"].denominator),
          "k = %d: the exponent exceeds the decimal target" % k)
    check(a > transfer, "k = %d: the exponent exceeds the transfer value" % k)

# ---------------------------------------------------------------------------
# 4.  The rational bounds of RK/Numeric.lean, and the assembly
# ---------------------------------------------------------------------------

print()
print("Rational bounds, as carried by RK/Numeric.lean")
for k in (4, 6):
    lo_sum = Fraction(0)
    hi_sum = Fraction(0)
    print("  k = %d" % k)
    for (m, sup, H) in POOLS[k]:
        t = len(sup)
        a = m ** (k - 1) * t
        (lp, lq), (hp, hq) = BOUNDS[k][m]
        lo = Fraction(lp, lq)
        hi = Fraction(hp, hq)
        # the two comparisons that RK/Numeric.lean settles by `decide`
        check(H ** lp < a ** lq,
              "k = %d, m = %d: %d^%d < %d^%d (lower bound)" % (k, m, H, lp, a, lq))
        check(m ** hq < H ** hp,
              "k = %d, m = %d: %d^%d < %d^%d (upper bound)" % (k, m, m, hq, H, hp))
        # and the same two facts in decimal, as a cross-check on the direction
        check(Decimal(lp) / Decimal(lq) < Decimal(a).ln() / Decimal(H).ln(),
              "k = %d, m = %d: lower bound below the true ratio" % (k, m))
        check(Decimal(m).ln() / Decimal(H).ln() < Decimal(hp) / Decimal(hq),
              "k = %d, m = %d: upper bound above the true ratio" % (k, m))
        print("    m=%4d t=%3d H=%3d  a = m^%d t = %-14d  log a / log H > %s   "
              "log m / log H < %s   (%d and %d digits)"
              % (m, t, H, k - 1, a, lo, hi, len(str(H ** lp)), len(str(m ** hq))))
        lo_sum += lo
        hi_sum += hi
    tgt = TARGETS[k]
    tp, tq = tgt["transfer_hi"]
    check(tgt["r"] ** tq < tgt["base"] ** tp,
          "k = %d: %d^%d < %d^%d (transfer upper bound)" % (k, tgt["r"], tq, tgt["base"], tp))
    assembled = lo_sum / (1 + k * hi_sum)
    transfer_hi = (Fraction(k - 1) + Fraction(tp, tq)) / k
    print("    log %d / log %d < %s, so the transfer value is below %s = %.12f"
          % (tgt["r"], tgt["base"], Fraction(tp, tq), transfer_hi, float(transfer_hi)))
    print("    assembled bound = (sum lo) / (1 + %d sum hi) = %.12f" % (k, float(assembled)))
    check(assembled > tgt["core"],
          "k = %d: the assembled bound exceeds the core decimal %s" % (k, float(tgt["core"])))
    check(tgt["core"] > tgt["decimal"],
          "k = %d: the core decimal exceeds the target %s" % (k, float(tgt["decimal"])))
    check(tgt["core"] > transfer_hi,
          "k = %d: the core decimal exceeds the transfer upper bound" % k)
    print("    clears %s by %.2e and the transfer value by %.2e"
          % (float(tgt["decimal"]), float(assembled - tgt["decimal"]),
             float(assembled - transfer_hi)))

# ---------------------------------------------------------------------------
# 5.  Controls: corruptions that the checker must reject
# ---------------------------------------------------------------------------

print()
print("Controls (each must be rejected)")

# A corrupted rank: in the block at m = 5 for k = 4 the arc 0 -> 1 exists (1 is a fourth-power
# residue mod 5), so raising the rank of vertex 1 from 2 to 3 destroys the strict drop.
bad_rank_4 = (5, [(0, 3), (1, 3), (2, 1), (3, 0)], 4)
# The same corruption in the block at m = 7 for k = 6: the arc 0 -> 1 exists.
bad_rank_6 = (7, [(0, 5), (1, 5), (2, 3), (3, 2), (4, 1), (5, 0)], 6)
# A corrupted vertex: replacing 3 by 4 in the block at m = 5 creates the arc 4 -> 0, along which
# the rank rises.  Likewise replacing 5 by 6 in the block at m = 7 creates the arc 6 -> 0.
bad_vertex_4 = (5, [(0, 3), (1, 2), (2, 1), (4, 0)], 4)
bad_vertex_6 = (7, [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (6, 0)], 6)

for k, (m, sup, H), label in ((4, bad_rank_4, "k = 4, rank of vertex 1 raised to 3"),
                              (6, bad_rank_6, "k = 6, rank of vertex 1 raised to 5"),
                              (4, bad_vertex_4, "k = 4, vertex 3 moved to 4"),
                              (6, bad_vertex_6, "k = 6, vertex 5 moved to 6")):
    ok, why = block_is_valid(k, m, sup, H)
    check(not ok, "control accepted a corrupted block (%s)" % label)
    print("  rejected (%s): %s" % (label, why))

print()
print("%d checks, %d failed" % (TOTAL, FAILED))
raise SystemExit(1 if FAILED else 0)
