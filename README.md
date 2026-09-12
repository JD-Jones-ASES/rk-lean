# rk-lean

A Lean 4 proof of the directed (acyclic-block) construction for sets of integers with no k-th-power
difference, at **every** exponent `k ≥ 2`, with two instances — `k = 4` and `k = 6` — whose
exponents exceed the values Ruzsa's residue transfer gives at those `k`.

**Start here.** Read the ten theorem statements in [Challenge.lean](Challenge.lean) and the nine
definitions above them; everything else in this repository exists to prove those ten statements
unchanged. [PROOF.md](PROOF.md) gives the mathematics in ordinary notation;
[VERIFICATION.md](VERIFICATION.md) the mechanical checks; [DISCLOSURE.md](DISCLOSURE.md) the
authorship and the automation.

## The problem

For `k ≥ 2` let `D_k(N)` be the largest size of a subset of `{1, …, N}` no two of whose elements
differ by a nonzero perfect k-th power. For `k = 2` this is the Furstenberg–Sárközy problem. Upper
bounds are all of the shape `N^{1−o(1)}` — Green–Sawhney's `N e^{−c√(log N)}` at `k = 2`
(arXiv:2411.17448), Balog–Pelikán–Pintz–Szemerédi at general fixed `k`
(Acta Math. Hungar. **65** (1994), 165–187, doi:10.1007/BF01874311), and Rice's maximal extension
to intersective polynomials of degree `k` (Acta Arith. **187** (2019), 1–41,
doi:10.4064/aa170828-26-8) — so the interesting question is how large an explicit construction can
get.

Every constructive lower bound comes from residues. Ruzsa's transfer (*Difference sets without
squares*, Period. Math. Hungar. **15** (1984), 205–209, doi:10.1007/BF02454169, Theorem 2) turns a
set of `r` residues modulo a square-free `m`, no two differing by a k-th-power residue, into
`D_k(N) ≫ N^{(k−1+log_m r)/k}`; Younis restates it in exactly that form (arXiv:1908.06058,
Theorem 1.4). Krachun (*Square-Difference-Free Sets beyond the Three-Quarter Barrier*,
arXiv:2608.01325, 2 Aug 2026) replaced the independent residue set by a residue set whose induced
digraph under "the difference is a nonzero square" is *acyclic*, carried with a ranking that
strictly decreases along every arc, and appended the rank as a high digit; his text treats squares
only. This repository states and proves a general-`k` form of that construction — the general
statement and its instances are this development's, not the source's — and instantiates it at
`k = 4` and `k = 6`.

## What is proved

* **The general theorem** (`KthPower.directed_liminf`, `KthPower.directed_pointwise`). For every
  `k ≥ 2` and every *pool* `P` for `k`,

      alpha k P ≤ liminf_{N→∞} log D_k(N) / log N,

  and `N^ρ ≤ D_k(N)` for all sufficiently large `N` whenever `ρ < alpha k P`. A pool is a nonempty
  list of blocks `(m, sup, H)` with pairwise coprime square-free moduli `m ≥ 2`, heights `H ≥ 2`,
  and `sup` a list of `(vertex, rank)` pairs with distinct vertices below `m`, ranks below `H`, and
  a strict rank drop along every arc — every ordered pair of vertices whose difference is a nonzero
  k-th-power residue modulo `m`. Writing `t` for the number of vertices of a block, the exponent is

      alpha k P = (Σ ((k−1) log m + log t) / log H) / (1 + k Σ log m / log H).

* **The two pools** (`KthPower.pool4_valid`, `KthPower.pool6_valid`). The nine blocks of `pool4`
  and the nine blocks of `pool6`, tabulated below, are pools for `k = 4` and `k = 6`; each of the
  eighteen block conditions is checked in the Lean kernel by `decide`.

* **The two instances** (`KthPower.fourth_power_liminf`, `KthPower.sixth_power_liminf`):
  `alpha 4 pool4 ≤ liminf log D_4(N)/log N` and `alpha 6 pool6 ≤ liminf log D_6(N)/log N`.

* **Where the two exponents sit** (`KthPower.alpha4_gt_transfer`, `KthPower.alpha4_gt`,
  `KthPower.alpha6_gt_transfer`, `KthPower.alpha6_gt`). The values are

      alpha 4 pool4 = 0.912145042700…       alpha 6 pool6 = 0.950825559086…

  and the four theorems prove `(3 + log 6/log 17)/4 < alpha 4 pool4`, `0.9121 < alpha 4 pool4`,
  `(5 + log 6/log 13)/6 < alpha 6 pool6` and `0.9508 < alpha 6 pool6`, each by exact comparisons of
  natural powers — no floating-point and no interval arithmetic anywhere in the development.

All ten are unconditional theorems, kernel-checked with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.

## The method

**Blocks and ranking.** Fix a square-free modulus `m` and let `Q` be the set of nonzero
k-th-power residues modulo `m` — the full image of `z ↦ z^k` on `ℤ/m` with `0` removed, non-units
included. A *block* is a set `S` of residues together with a ranking `h : S → {0, …, H−1}` such
that `y − x ∈ Q` forces `h(y) < h(x)`. Such a ranking exists exactly when the digraph on `S` with
those arcs is acyclic, so acyclicity is not a separate hypothesis; it is what having a ranking
means. Ruzsa's transfer is the case of a block with no arcs at all — an independent residue set,
for which any ranking will do — and the point of the directed method is that a block may be much
larger than any independent set, at the cost of a height `H > 1` that has to be paid for in the
denominator of the exponent.

**Three lemmas.** *Lemma A, the lift* (`KthPower.lemmaA`): a block `S` on `ℤ/m` lifts, for each
multiplicity `e ≥ 1`, to a block on `ℤ/m^{ke}` — the residues whose base-`m` digits at the
positions `k·0, k·1, …, k(e−1)` all lie in `S`, ranked by the base-`H` number
`Σ_{j<e} h(x_{kj}) H^{e−1−j}`. It has `(m^{k−1}|S|)^e` elements (`e` constrained digits and
`e(k−1)` free ones) and height `H^e`. The argument is a valuation argument: if the difference
`d` of two lifted residues is a nonzero k-th-power residue, then in any coordinate not saturated by
the modulus `v_q(d) = k v_q(z)`, so `v_m(d)` — which square-freeness makes the minimum of the
`v_q(d)` — is a multiple of `k`; the least differing digit position is therefore one of the
constrained ones, its digit difference is again in `Q`, and the lifted ranking drops.
*Lemma B, the passage to integers* (`KthPower.lemmaB_pdf`): if the modulus is a perfect k-th power
`P = n^k`, then words of length `L` over a block, displaced by `P^L` times their word rank, form a
set of `|S|^L` integers inside `{1, …, (PH)^L}` with no k-th-power difference — here `P^j ∣ z^k`
gives `n^j ∣ z` outright, so no primality and no square-freeness is needed.
*Lemma C, the glue* (`KthPower.lemmaC`, `KthPower.glueList_rankedBlock`): blocks on coprime moduli
combine by the Chinese remainder theorem, supports multiplying and heights adding as
`H = 1 + Σ (H_i − 1)`.

**The exponent.** Lifting the `i`-th block of the pool with multiplicity `e_i` and gluing gives a
block on `Π m_i^{k e_i}` of size `Π (m_i^{k−1} t_i)^{e_i}` and height `1 + Σ (H_i^{e_i} − 1)`;
Lemma B turns it into `D_k((PH)^L) ≥ |C|^L`. Taking `e_i = ⌊U / log H_i⌋` makes every
`H_i^{e_i}` equal to `e^{U+O(1)}`, so `log H = U + O(1)` while `log P` and `log|C|` are linear in
`U`, and the ratio `log|C| / log(PH)` tends to `alpha k P`; a standard sandwich
`B^L ≤ N < B^{L+1}` carries the bound from the special values to every `N`, and the liminf
statement follows. The formula displays the trade directly: each block contributes
`log(m^{k−1} t)` to the numerator and `k log m` to the denominator, both per unit of `log H`, and
the isolated `1` in the denominator is the height's own cost.

**Why the method exists exactly at even `k`.** The cheapest source of arcs is antisymmetry: the
relation "`y − x` is a nonzero k-th-power residue" is a genuine *digraph* relation whenever `−1` is
not a k-th-power residue. Modulo a prime `p` with `p − 1` divisible by `k`, `−1` is a k-th power
exactly when `2k ∣ p − 1`; so the primes with `Q ∩ (−Q) = ∅` are those `≡ 5 (mod 8)` at `k = 4`
and those `≡ 7 (mod 12)` at `k = 6`. Every prime modulus of the two pools is of that kind — the
eight primes `5, 13, 29, 37, 53, 61, 101, 109` of `pool4` and all nine moduli of `pool6` — and at
each of them at most one of `y − x`, `x − y` lies in `Q` for distinct `x, y`: the arcs really are
oriented, and a block can be large and still acyclic. At **odd** `k`, by contrast,
`−1 = (−1)^k` is always a k-th-power residue, so
`Q = −Q` and the relation is symmetric: an arc `x → y` would force `h(y) < h(x)` and `h(x) < h(y)`
at once, so every valid block is an *independent* set. The general theorem is still true there,
but it is then weaker than Ruzsa's transfer, whose denominator is `k log m` where this one has
`k log m + log H`. The interest is at even `k`.

The smallest block at each even `k` is the analogue of Krachun's prime `3`. At `p = k + 1` (prime)
the multiplicative group has order `k`, so `Q = {1}`, and the digraph on `ℤ/p` is the single chain
`x → x + 1`: the `k` residues `0, 1, …, k−1` with ranks `k−1, …, 0` form a block with `t = H = k`.
That is `(3, 2, 2)` at `k = 2`, `(5, 4, 4)` at `k = 4` and `(7, 6, 6)` at `k = 6` — the first row
of each table below, and the highest-yield block of each pool.

**A second source of acyclicity: intervals.** Antisymmetry is sufficient but not necessary. If
`t ≤ m − max Q`, then any `t` consecutive residues form a block. For `x` before `y` in the
interval the difference `y − x` lies in `{1, …, t−1}` and may or may not be an arc; for `y` before
`x` it is one of `m−t+1, …, m−1`, every one of which exceeds `max Q` and so is not an arc at all.
Every arc therefore runs forward in the interval order, which is itself a ranking, and the block
is acyclic of height `t`. One block of `pool4` is of this kind, at the composite square-free
modulus `51 = 3 · 17`: the fourth-power residues modulo `51` are
`{1, 4, 13, 16, 18, 21, 30, 33, 34}`, with maximum `34`, so the `t = 51 − 34 = 17` consecutive
residues `35, 36, …, 50, 0` form a block of height `17`, ranked `16, 15, …, 1, 0`. Neither reason
above applies to it: `51` is not a prime of either congruence class (`3 ≡ 3 (mod 8)`,
`17 ≡ 1 (mod 8)`), and the relation modulo `51` is not antisymmetric, since `18` and `−18 = 33`
are both fourth-power residues. The interval argument is doing the work, and `ValidPool` asks for
nothing more — square-free moduli, pairwise coprime, and a ranking. Its seventeen vertices are the
largest ranked support at `51` (an exhaustive search outside the formal development).

## The two pools

The blocks were found by computer search (see [DISCLOSURE.md](DISCLOSURE.md)); they are lower-bound
witnesses, and nothing here claims maximality as a theorem — no statement in Lean asserts that any
support is largest possible or any height least possible. As context: the sizes at
`5, 13, 29, 37, 51, 53, 61` for `k = 4` and at `7, 19, 31, 43` for `k = 6` are exact maxima, by
exhaustive search outside Lean; at the larger moduli the sizes are the best the search reached.
`H` is the height actually stored and verified — the number of rank values the block uses, which
for every block here is the length of a longest path in its digraph. `log_m t` is the yield of the
block read as a residue set, for comparison with the transfer exponent `(k − 1 + log_m t)/k`.

**`pool4` (`k = 4`, nine blocks, 126 vertices in all; the eight prime moduli are `≡ 5 mod 8`, and
`51 = 3 · 17` is the interval block).**

| `m` | `t` | `H` | `log_m t` |
| --- | --- | --- | --- |
| 5 | 4 | 4 | 0.861353 |
| 13 | 7 | 4 | 0.758654 |
| 29 | 12 | 11 | 0.737953 |
| 37 | 13 | 11 | 0.710332 |
| 51 | 17 | 17 | 0.720585 |
| 53 | 16 | 8 | 0.698334 |
| 61 | 16 | 10 | 0.674452 |
| 101 | 20 | 12 | 0.649112 |
| 109 | 21 | 8 | 0.648965 |

**`pool6` (`k = 6`, nine blocks, 196 vertices in all; every modulus a prime `≡ 7 mod 12`).**

| `m` | `t` | `H` | `log_m t` |
| --- | --- | --- | --- |
| 7 | 6 | 6 | 0.920782 |
| 19 | 10 | 3 | 0.782011 |
| 31 | 15 | 9 | 0.788602 |
| 43 | 18 | 6 | 0.768471 |
| 67 | 23 | 14 | 0.745713 |
| 79 | 27 | 17 | 0.754291 |
| 103 | 30 | 13 | 0.733850 |
| 127 | 33 | 9 | 0.721794 |
| 139 | 34 | 22 | 0.714638 |

The nine moduli of `pool4` are pairwise coprime even though `51` is composite: `3` and `17` occur
in no other block. The vertex lists and the rank of each vertex are in
[Challenge.lean](Challenge.lean).

## What the exponents are compared against

**`k = 6`.** The transfer value `(5 + log 6/log 13)/6 = 0.949759249243…` is Ruzsa's own published
Corollary at `k = 6`: `d_k ≥ 1 − 1/k + log k/(k log p(2k))` with `p(12) = 13` the least prime
`≡ 1 (mod 12)`, and `13` does carry six residues with no sixth-power difference — the sixth powers
modulo `13` are `{1, 12}`, and `{0, 2, 4, 6, 8, 10}` avoids them, maximally (again an exhaustive
check outside the formal development). Ruzsa printed only the
`k = 3` and `k = 5` instances (`0.854858…` and `0.934237…`), but `0.949759…` is his value, not a
new one. `alpha 6 pool6 = 0.950825559086…` exceeds it by `1.07 × 10⁻³`.

**`k = 4`.** Two rungs have to be distinguished. Ruzsa's Corollary at `k = 4` gives
`1 − 1/4 + log 4/(4 log 17) = 0.872325271059…` (`p(8) = 17`, `r = 4`), and that is the only
*published* value for fourth powers. The stronger transfer rung `(3 + log 6/log 17)/4 =
0.908103119289…` needs **six** residues modulo `17` with no fourth-power difference, and no search
found any publication exhibiting such a set or stating that exponent. It exists: the fourth powers
modulo `17` are `{1, 4, 13, 16}`, and

      {0, 2, 5, 7, 10, 12}   mod 17

has no two elements whose difference is one of them, and six is the maximum, by exhaustive check
over all subsets of `ℤ/17`. Both of those are computations outside the formal development — the
Lean theorem mentions only the real number `(3 + log 6/log 17)/4`; see the "Not checked here"
section of [VERIFICATION.md](VERIFICATION.md). `alpha 4 pool4 = 0.912145042700…` exceeds that
unpublished rung by `4.04 × 10⁻³`, and the published rung by `3.98 × 10⁻²`. The theorem in Lean is
the comparison against the `0.908103…` rung, the harder of the two.

**For context, the rest of the landscape.** The best published exponent for cubes is Lewko's
`2/3 + log 14/(3 log 91) = 0.861681779699…`, from fourteen residues modulo `91`
(*An improved lower bound related to the Furstenberg–Sárközy theorem*, Electron. J. Combin. **22**
(2015), no. 1, P1.32, Theorem 4, doi:10.37236/4656) — a transfer value, and `k = 3` is odd, so the
directed method says nothing new there. At `k = 2` the best published exponent is Krachun's
`0.752796455875…`, by the directed method itself, above the `0.733411797040…` of the transfer at
`m = 205` (Beigel–Gasarch, arXiv:0804.4892; Lewko 2015, Theorem 3).

**A ceiling the directed method escapes — cited context, outside the formal development.** Nothing
in this paragraph is a theorem of this repository, and none of it is formalized here. Every
*independent*-residue-set construction at square-free `m` is capped. By the Chinese remainder
theorem the Cayley graph of `ℤ/m` on `±`(k-th powers) is the strong product of the per-prime
Cayley graphs; `ϑ` bounds the independence number and is multiplicative under the strong product,
so `log_m r_k(m) ≤ max_{p ∣ m} log_p ϑ` and the transfer exponent cannot exceed
`(k − 1 + c_k)/k` with `c_k = max_p log_p ϑ(Cay(ℤ/p, ± k-th powers))`, `ϑ` the theta function of
Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory **25** (1979), no. 1,
1–7, doi:10.1109/TIT.1979.1055985. Each prime graph is edge-transitive, so its `ϑ` is the Lovász ratio bound `−n λ_min/(λ_max − λ_min)` in
its eigenvalues (Gauss periods), and the Weil bound shows `log_p ϑ` decreases for large `p`; evaluating
the maximum over primes — a computation, not a theorem, and not checked in Lean — puts it at
`p = 41` for `k = 4` and `p = 157` for `k = 6`, and the ceiling at `0.924871` for `k = 4` and
`0.956627` for `k = 6`. The exponents proved here, `0.912145…` and `0.950826…`, are still below
those two numbers — but they are not bound by them, because the blocks of a pool are acyclic
vertex sets, not independent ones, and the theta bound does not apply to them. That is the
structural reason to expect the directed method to go further than any residue-set transfer can.

## Files

* [Challenge.lean](Challenge.lean) — the ten statements and the nine definitions, using only
  Mathlib, with `sorry` placeholders; the surface a reader should audit.
* [Solution.lean](Solution.lean) — the same ten statements, proved from the library `RK`. It does
  not import `Challenge.lean`.
* `RK/` — the development: `Defs` (the nine definitions, generated from the Challenge),
  `DiffMod` (the residue-difference toolkit), `RankedBlocks` (the functional form of a block),
  `LemmaA` (digits and the composite lift), `LemmaB` (words and the passage to integers),
  `LemmaC` (the Chinese-remainder glue), `Construction` (the stage moduli, sizes and heights),
  `Asymptotics` (the allocation, the limit, and the passage to all `N`), `Pools` (the eighteen
  block verifications), `Numeric` (the exponent inequalities), `Main` (the ten targets).
* [Test/Axioms.lean](Test/Axioms.lean) — the axiom audit over every declaration of the
  development.
* [scripts/check_blocks.py](scripts/check_blocks.py) — a standalone check (Python ≥ 3.9, standard
  library only) of the blocks, the moduli, the exponents, the rational bounds and the two transfer
  values, with controls that must fail.
* [scripts/check-source.py](scripts/check-source.py) — rejects `sorry`, `axiom`, `native_decide`
  and similar tokens in `RK/`, `Solution.lean` and `Test/`.
* [PROOF.md](PROOF.md) — the statements and the proofs in ordinary mathematics, with the Lean name
  of every step. [VERIFICATION.md](VERIFICATION.md) — the checks performed at this snapshot and how
  to repeat them. [DISCLOSURE.md](DISCLOSURE.md) — authorship and the use of AI.
* [formalization.yaml](formalization.yaml), [comparator.json](comparator.json) — registry metadata
  and the statement-comparison configuration.

## Verify

Install [Elan](https://github.com/leanprover/elan); the toolchain is `leanprover/lean4:v4.33.0`
and Mathlib is pinned in `lake-manifest.json`. Then:

```sh
lake exe cache get
lake build
python3 scripts/check-source.py
python3 scripts/check_blocks.py
```

`lake build` compiles the library `RK`, `Challenge`, `Solution` and `Test`; the axiom audit in
`Test` fails the build on any unexpected axiom, on too few audited constants, or on a missing
compared theorem. The expected output is ten `declaration uses sorry` warnings from
`Challenge.lean` — its intentional placeholders, one per pinned theorem — and nothing else.
[VERIFICATION.md](VERIFICATION.md) has the details.

## Prior art

**Prior art (searched 2026-09-12).** Ruzsa's transfer already covers every k (Theorem 2 and its
Corollary in *Difference sets without squares*, Period. Math. Hungar. **15** (1984), 205–209,
doi:10.1007/BF02454169), giving `d_k ≥ 1 − 1/k + log r_k(m)/(k log m)` and, for the least prime
`p ≡ 1 mod 2k`, the explicit values `d_3 ≥ 0.854858…`, `d_5 ≥ 0.934237…`, and at `k = 4, 6` the
instances `0.872325…` (`m = 17`) and `0.949759…` (`m = 13`); the best published exponent for
cubes is Lewko's `2/3 + log 14/(3 log 91) = 0.861681…` from fourteen residues mod 91
(*An improved lower bound related to the Furstenberg–Sárközy theorem*, Electron. J. Combin. **22**
(2015), no. 1, P1.32, Theorem 4, doi:10.37236/4656), and the general-k transfer is restated as
Theorem 1.4 of K. Younis, *Lower bounds in the polynomial Szemerédi theorem*, arXiv:1908.06058.
Krachun's directed construction (*Square-Difference-Free Sets beyond the Three-Quarter Barrier*,
arXiv:2608.01325, 2 Aug 2026) is stated for `k = 2` only — its text never mentions powers other
than squares — and a survey of the general-k problem published in 2025
(Georgiev–Gómez-Serrano–Tao–Wagner, *Mathematical exploration and discovery at scale*,
arXiv:2511.02864, Problem 6.31) records values for `k = 2` and `k = 3` only, reporting that an
automated search reproduced the moduli 205 and 91 without improving them. A search on 2026-09-12
of arXiv (metadata sweep plus full text of the relevant papers), web search, Crossref, the
Semantic Scholar citation graph of arXiv:2608.01325, Mathlib4 (authenticated code search), the
Isabelle AFP (all 1027 entries) and the Palomar registry (all 228 entries via its CC0 data API)
found no lower bound for `D_k(N)` at `k ≥ 4` beyond Ruzsa's Corollary, no exponent above
`0.861681…` for cubes, no directed or acyclic construction for any `k > 2`, and no formalization
in any proof assistant of Ruzsa's transfer, of Krachun's lemmas, or of any `k`-th-power-difference
lower bound at `k ≥ 3`. The only formalizations found in this problem area are this author's own
earlier entries — PALOMAR-2026-08-26-000004 (`fs-formal`, the `k = 2` Furstenberg–Sárközy exponent
`0.7537 < α∞`) and PALOMAR-2026-09-11-000003 (`ry-lean`, the configuration `{x, x + y, x + y²}` at
exponent `0.770287…`) — which this development builds on rather than supersedes.

Two further attributions. The *ranking* of a block is Krachun's: his Definition 2 is a "Paley
chain" and his Lemma 3 a "local ranked block". Reading the same object as an acyclic digraph
under "the difference is a nonzero k-th-power residue", carried with a topological ranking, is
this development's reformulation and is not attributed to him. The GitHub-wide code search outside
Mathlib4 hit an API rate limit on 2026-09-12 and is therefore incomplete; the negative
formalization statements above rest on the venues that were swept completely.

## Authorship

JD Jones is the human author and responsible maintainer. He is not a party to the mathematics.
The directed method with a ranking is Dmitry Krachun's, at `k = 2`; the residue transfer is Imre
Ruzsa's; Anthropic's Claude models wrote the Lean development and this documentation under
JD Jones's direction, and the blocks of the two pools were found by computer search — see
[DISCLOSURE.md](DISCLOSURE.md). No independent human expert review is recorded.

License: [MIT](LICENSE).
