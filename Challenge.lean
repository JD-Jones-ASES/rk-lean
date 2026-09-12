import Mathlib

/-!
# Sets of integers with no k-th-power difference: the directed construction

For `k ≥ 2` let `D_k(N)` be the largest size of a subset of `{1, …, N}` no two of whose
elements differ by a nonzero k-th power. Every constructive lower bound for `D_k(N)` comes from
residues: Ruzsa (*Difference sets without squares*, 1984) transfers a k-th-power-difference-free
set of `r` residues modulo a square-free `m` into `D_k(N) ≫ N^((k − 1 + log_m r) / k)`, and
Krachun (*Square-Difference-Free Sets beyond the Three-Quarter Barrier*, arXiv:2608.01325, for
`k = 2`) replaced independent residue sets by residue sets whose induced digraph is *acyclic*,
carried with a ranking that strictly decreases along every arc; his paper treats squares only.
This file states a general-`k` form of that ranked-block construction (the general statement and
its instances are this development's, not the source's), together with two instances, at `k = 4`
and `k = 6`, whose exponents exceed the corresponding transfer values.

## The objects

Write `Q` for the set of nonzero k-th-power residues modulo `m`, the full image of `z ↦ z ^ k` on
`ℤ/m` with `0` removed (non-units included). A **ranked support** modulo `m` of height `H` is a
list of pairs `(vertex, rank)`: distinct vertices below `m`, ranks below `H`, and along every
ordered pair of vertices whose difference lies in `Q` the rank strictly drops. A **pool** for `k`
is a nonempty list of blocks `(m, sup, H)` with pairwise coprime square-free moduli `m ≥ 2`,
heights `H ≥ 2`, and `sup` a nonempty ranked support modulo `m` of height `H`. Its **exponent** is

  `alpha k P = (Σ ((k − 1) log m + log t) / log H) / (1 + k Σ log m / log H)`,

the sums over the blocks, with `t ≥ 1` the number of vertices of the block.

## What is claimed

* `directed_liminf`, `directed_pointwise`: for every `k ≥ 2` and every pool `P` for `k`,
  `alpha k P ≤ liminf log D_k(N) / log N`, and `N ^ ρ ≤ D_k(N)` for all large `N` whenever
  `ρ < alpha k P`.
* `pool4_valid`, `pool6_valid`: the two concrete lists below are pools for `k = 4` and `k = 6`.
* `alpha4_gt_transfer`, `alpha4_gt`: `alpha 4 pool4` exceeds the transfer value
  `(3 + log 6 / log 17) / 4 = 0.908103…` and `0.9121` (its value is `0.912145…`).
* `alpha6_gt_transfer`, `alpha6_gt`: `alpha 6 pool6` exceeds the transfer value
  `(5 + log 6 / log 13) / 6 = 0.949759…` and `0.9508` (its value is `0.950826…`).
* `fourth_power_liminf`, `sixth_power_liminf`: the two instances of `directed_liminf`.

## Conventions

All finite objects are natural numbers: a residue modulo `m` is a natural number below `m`, and
`diffMod m a b = (b + m − a) % m` is the residue of `b − a`. Sets of integers are `Finset ℕ`; a set
is k-th-power-difference-free when no element plus a positive k-th power is again an element,
which covers both signs of the difference. `D k N` is a maximum over the subsets of
`{1, …, N}`. Logarithms are natural logarithms. `Squarefree` is Mathlib's.

This Mathlib-only file intentionally contains `sorry` placeholders. The corresponding
declarations are proved in `Solution.lean`, which does not import this file.
-/

namespace KthPower

/-- `d` (already reduced mod `m`) is a nonzero k-th-power residue modulo `m`: `d ≠ 0` and some
`z < m` has `z ^ k ≡ d (mod m)`. The image of `z ↦ z ^ k` is taken in full, non-units included. -/
def IsNonzeroPowerMod (k m d : ℕ) : Prop :=
  d % m ≠ 0 ∧ ∃ z < m, z ^ k % m = d % m

/-- A kernel-friendly decision procedure: search `z` over `List.range m`. -/
instance instDecidableIsNonzeroPowerMod (k m d : ℕ) : Decidable (IsNonzeroPowerMod k m d) :=
  decidable_of_iff
    (d % m ≠ 0 ∧ ((List.range m).any fun z => z ^ k % m == d % m) = true) <| by
      simp [IsNonzeroPowerMod, List.any_eq_true, List.mem_range]

/-- The residue of `b − a` modulo `m`, for `a b < m`, computed in `ℕ`. -/
def diffMod (m a b : ℕ) : ℕ := (b + m - a) % m

/-- A ranked support modulo `m` of height `H`, as a list of `(vertex, rank)` pairs: vertices
pairwise distinct and `< m`, ranks `< H`, and along every arc — every ordered pair of vertices
whose difference is a nonzero k-th-power residue mod `m` — the rank strictly drops. The induced
digraph is acyclic because such a ranking exists; acyclicity is not a separate condition. -/
def ValidRankedSupport (k m : ℕ) (sup : List (ℕ × ℕ)) (H : ℕ) : Prop :=
  sup.Pairwise (fun p q => p.1 ≠ q.1) ∧
  (∀ p ∈ sup, p.1 < m ∧ p.2 < H) ∧
  ∀ p ∈ sup, ∀ q ∈ sup, p.1 ≠ q.1 →
    IsNonzeroPowerMod k m (diffMod m p.1 q.1) → q.2 < p.2

instance instDecidableValidRankedSupport (k m : ℕ) (sup : List (ℕ × ℕ)) (H : ℕ) :
    Decidable (ValidRankedSupport k m sup H) := by
  unfold ValidRankedSupport; infer_instance

/-- A pool for `k`: a nonempty list of blocks `(m, sup, H)` whose moduli are pairwise coprime,
each modulus `m ≥ 2` square-free, each height `H ≥ 2`, and each `sup` a nonempty ranked support
modulo `m` of height `H`. -/
def ValidPool (k : ℕ) (P : List (ℕ × List (ℕ × ℕ) × ℕ)) : Prop :=
  P ≠ [] ∧ (P.map Prod.fst).Pairwise Nat.Coprime ∧
  ∀ b ∈ P, 2 ≤ b.1 ∧ Squarefree b.1 ∧ 2 ≤ b.2.2 ∧ b.2.1 ≠ [] ∧
    ValidRankedSupport k b.1 b.2.1 b.2.2

/-- The exponent of a pool: `(Σ ((k − 1) log m + log t) / log H) / (1 + k Σ log m / log H)`,
where `t` is the length of the block's support list (its number of vertices, the vertices being
distinct). -/
noncomputable def alpha (k : ℕ) (P : List (ℕ × List (ℕ × ℕ) × ℕ)) : ℝ :=
  (P.map fun b =>
    (((k : ℝ) - 1) * Real.log b.1 + Real.log b.2.1.length) / Real.log b.2.2).sum /
  (1 + (k : ℝ) * (P.map fun b => Real.log b.1 / Real.log b.2.2).sum)

/-- No element of `A` plus a positive k-th power is again in `A`; equivalently, no two elements
of `A` differ by a nonzero k-th power (both signs of the difference are covered). -/
def PowerDifferenceFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ z : ℕ, 0 < z → a + z ^ k ∉ A

/-- `D k N` is the largest size of a k-th-power-difference-free subset of `{1, …, N}`.
`D` is never computed, so the filter is given a classical decidability instance. -/
noncomputable def D (k N : ℕ) : ℕ :=
  letI := Classical.decPred (PowerDifferenceFree k)
  ((Finset.Icc 1 N).powerset.filter (PowerDifferenceFree k)).sup Finset.card

/-- **The directed construction at every `k`, liminf form.** For `k ≥ 2` and every pool `P`
for `k`, `alpha k P ≤ liminf log D_k(N) / log N`. -/
theorem directed_liminf (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) :
    alpha k P ≤ Filter.liminf (fun N : ℕ => Real.log (D k N) / Real.log N) Filter.atTop := by
  sorry

/-- **The directed construction at every `k`, pointwise form.** For `k ≥ 2`, every pool `P` for
`k` and every `ρ < alpha k P`, `N ^ ρ ≤ D_k(N)` for all sufficiently large `N`. -/
theorem directed_pointwise (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  sorry

/-- The pool for `k = 4`: nine blocks, one at each prime `5, 13, 29, 37, 53, 61, 101, 109` and one
at the composite modulus `51 = 3 · 17`, as `(m, [(vertex, rank), …], H)`, in increasing order of
`m`. Sizes `4, 7, 12, 13, 17, 16, 16, 20, 21`; heights `4, 4, 11, 11, 17, 8, 10, 12, 8`. -/
def pool4 : List (ℕ × List (ℕ × ℕ) × ℕ) :=
  [(5, [(0, 3), (1, 2), (2, 1), (3, 0)], 4),
   (13, [(0, 0), (2, 2), (5, 1), (7, 2), (8, 0), (10, 1), (12, 3)], 4),
   (29, [(0, 7), (1, 6), (2, 5), (3, 2), (5, 9), (6, 8), (14, 10), (15, 9), (16, 3), (17, 0),
     (25, 4), (26, 1)], 11),
   (37, [(0, 9), (3, 10), (5, 1), (8, 10), (10, 6), (13, 7), (15, 0), (18, 9), (20, 3), (23, 4),
     (26, 5), (32, 2), (34, 8)], 11),
   (51, [(0, 0), (35, 16), (36, 15), (37, 14), (38, 13), (39, 12), (40, 11), (41, 10), (42, 9),
     (43, 8), (44, 7), (45, 6), (46, 5), (47, 4), (48, 3), (49, 2), (50, 1)], 17),
   (53, [(0, 0), (3, 0), (5, 5), (6, 1), (8, 2), (11, 6), (14, 6), (17, 7), (29, 1), (32, 1),
     (35, 2), (37, 3), (38, 2), (40, 7), (41, 4), (43, 7)], 8),
   (61, [(0, 1), (4, 6), (7, 7), (14, 4), (17, 5), (24, 2), (27, 3), (31, 7), (35, 9), (37, 1),
     (41, 5), (45, 8), (47, 0), (51, 3), (55, 8), (57, 0)], 10),
   (101, [(0, 0), (3, 9), (6, 2), (10, 5), (11, 1), (13, 9), (14, 6), (15, 3), (17, 10), (18, 7),
     (21, 11), (28, 7), (29, 4), (32, 8), (57, 7), (61, 8), (69, 0), (72, 5), (75, 9), (76, 6)
     ], 12),
   (109, [(0, 0), (2, 0), (4, 2), (12, 2), (34, 1), (36, 7), (42, 0), (44, 6), (46, 7), (52, 1),
     (54, 4), (62, 6), (71, 5), (76, 3), (84, 1), (86, 4), (88, 5), (94, 4), (95, 3), (101, 0),
     (103, 1)], 8)]

/-- The pool for `k = 6`: nine blocks, one at each prime `7, 19, 31, 43, 67, 79, 103, 127, 139`.
Sizes `6, 10, 15, 18, 23, 27, 30, 33, 34`; heights `6, 3, 9, 6, 14, 17, 13, 9, 22`. -/
def pool6 : List (ℕ × List (ℕ × ℕ) × ℕ) :=
  [(7, [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)], 6),
   (19, [(0, 1), (2, 0), (4, 2), (5, 1), (6, 0), (8, 2), (10, 1), (11, 0), (14, 1), (15, 0)], 3),
   (31, [(0, 8), (2, 7), (4, 6), (6, 5), (7, 3), (9, 2), (11, 1), (13, 0), (16, 7), (18, 6),
     (20, 5), (22, 4), (24, 3), (26, 2), (28, 1)], 9),
   (43, [(0, 2), (2, 5), (3, 4), (6, 4), (7, 1), (12, 2), (13, 1), (16, 1), (17, 0), (19, 3),
     (22, 3), (23, 0), (25, 5), (26, 1), (31, 1), (36, 3), (37, 0), (40, 2)], 6),
   (67, [(0, 9), (1, 5), (2, 3), (4, 6), (8, 12), (10, 4), (14, 1), (17, 2), (20, 3), (26, 0),
     (30, 10), (33, 11), (37, 13), (39, 0), (43, 11), (46, 12), (47, 8), (49, 13), (55, 9),
     (56, 7), (58, 10), (59, 8), (65, 4)], 14),
   (79, [(0, 9), (2, 12), (5, 1), (7, 4), (8, 1), (14, 16), (19, 13), (20, 11), (22, 8), (24, 5),
     (25, 2), (30, 0), (36, 14), (37, 12), (39, 15), (42, 3), (44, 7), (45, 1), (49, 13),
     (56, 16), (58, 10), (61, 14), (62, 2), (65, 6), (67, 0), (74, 3), (78, 15)], 17),
   (103, [(0, 4), (2, 8), (4, 8), (7, 12), (8, 0), (11, 7), (13, 3), (15, 0), (18, 7), (19, 6),
     (20, 0), (25, 1), (30, 1), (35, 9), (36, 0), (40, 8), (47, 2), (51, 5), (52, 4), (57, 10),
     (62, 10), (63, 1), (67, 11), (68, 0), (78, 6), (83, 5), (85, 2), (88, 11), (90, 6), (95, 5)
     ], 13),
   (127, [(0, 4), (1, 1), (4, 0), (7, 5), (13, 2), (16, 1), (22, 1), (27, 7), (28, 2), (31, 1),
     (40, 6), (43, 6), (44, 1), (49, 5), (55, 6), (57, 0), (64, 3), (67, 8), (70, 7), (71, 4),
     (79, 3), (84, 6), (85, 2), (86, 0), (92, 0), (97, 8), (99, 4), (101, 0), (106, 7), (112, 6),
     (113, 1), (114, 0), (119, 5)], 9),
   (139, [(0, 16), (1, 11), (5, 19), (11, 12), (20, 1), (25, 14), (30, 2), (31, 0), (40, 12),
     (41, 5), (43, 2), (45, 7), (46, 6), (48, 17), (50, 16), (55, 8), (57, 4), (60, 17),
     (62, 18), (69, 9), (71, 18), (73, 21), (78, 9), (90, 5), (91, 3), (97, 0), (113, 6),
     (115, 14), (116, 13), (117, 10), (118, 4), (128, 16), (129, 15), (138, 20)], 22)]

/-- The list `pool4` is a pool for `k = 4`. -/
theorem pool4_valid : ValidPool 4 pool4 := by
  sorry

/-- The list `pool6` is a pool for `k = 6`. -/
theorem pool6_valid : ValidPool 6 pool6 := by
  sorry

/-- The exponent at `k = 4` exceeds the transfer value `(3 + log 6 / log 17) / 4 = 0.908103…`
obtained from the six fourth-power-difference-free residues modulo `17`. -/
theorem alpha4_gt_transfer : (3 + Real.log 6 / Real.log 17) / 4 < alpha 4 pool4 := by
  sorry

/-- A decimal lower bound for the exponent at `k = 4` (its value is `0.912145…`). -/
theorem alpha4_gt : (0.9121 : ℝ) < alpha 4 pool4 := by
  sorry

/-- The exponent at `k = 6` exceeds the transfer value `(5 + log 6 / log 13) / 6 = 0.949759…`
obtained from the six sixth-power-difference-free residues modulo `13`. -/
theorem alpha6_gt_transfer : (5 + Real.log 6 / Real.log 13) / 6 < alpha 6 pool6 := by
  sorry

/-- A decimal lower bound for the exponent at `k = 6` (its value is `0.950826…`). -/
theorem alpha6_gt : (0.9508 : ℝ) < alpha 6 pool6 := by
  sorry

/-- **Fourth powers:** `alpha 4 pool4 ≤ liminf log D_4(N) / log N`. -/
theorem fourth_power_liminf :
    alpha 4 pool4 ≤ Filter.liminf (fun N : ℕ => Real.log (D 4 N) / Real.log N) Filter.atTop := by
  sorry

/-- **Sixth powers:** `alpha 6 pool6 ≤ liminf log D_6(N) / log N`. -/
theorem sixth_power_liminf :
    alpha 6 pool6 ≤ Filter.liminf (fun N : ℕ => Real.log (D 6 N) / Real.log N) Filter.atTop := by
  sorry

end KthPower
