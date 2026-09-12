import Mathlib

/-!
# Definitions

The nine definitions and two decidability instances of `Challenge.lean`, character for character.
`RK/Defs.lean` is generated from `Challenge.lean` and must not be edited by hand; the toolkit
lemmas about `diffMod` live in `RK/DiffMod.lean`.

* `IsNonzeroPowerMod k m d` — `d` is a nonzero k-th-power residue mod `m` (full image, non-units
  included), with a `List.range` search as its decision procedure;
* `diffMod m a b` — the residue of `b − a` mod `m` in `ℕ`;
* `ValidRankedSupport k m sup H` — the decidable list form of a ranked block;
* `ValidPool k P` — a nonempty list of blocks on pairwise coprime square-free moduli;
* `alpha k P` — the exponent of a pool;
* `PowerDifferenceFree k A`, `D k N` — the counting function;
* `pool4`, `pool6` — the two concrete pools.
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
each modulus `m ≥ 2` square-free, each height `H ≥ 2`, and each `sup` a ranked support modulo
`m` of height `H`. -/
def ValidPool (k : ℕ) (P : List (ℕ × List (ℕ × ℕ) × ℕ)) : Prop :=
  P ≠ [] ∧ (P.map Prod.fst).Pairwise Nat.Coprime ∧
  ∀ b ∈ P, 2 ≤ b.1 ∧ Squarefree b.1 ∧ 2 ≤ b.2.2 ∧ ValidRankedSupport k b.1 b.2.1 b.2.2

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

/-- The pool for `k = 4`: eight blocks, one at each prime `5, 13, 29, 37, 53, 61, 101, 109`, as
`(m, [(vertex, rank), …], H)`. Sizes `4, 7, 12, 13, 16, 16, 20, 21`; heights
`4, 4, 11, 11, 8, 10, 12, 8`. -/
def pool4 : List (ℕ × List (ℕ × ℕ) × ℕ) :=
  [(5, [(0, 3), (1, 2), (2, 1), (3, 0)], 4),
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
     (21, 11), (28, 7), (29, 4), (32, 8), (57, 7), (61, 8), (69, 0), (72, 5), (75, 9), (76, 6)],
     12),
   (109, [(0, 0), (2, 0), (4, 2), (12, 2), (34, 1), (36, 7), (42, 0), (44, 6), (46, 7), (52, 1),
     (54, 4), (62, 6), (71, 5), (76, 3), (84, 1), (86, 4), (88, 5), (94, 4), (95, 3), (101, 0),
     (103, 1)], 8)]

/-- The pool for `k = 6`: nine blocks, one at each prime `7, 19, 31, 43, 67, 79, 103, 127, 139`.
Sizes `6, 10, 15, 18, 23, 27, 30, 33, 34`; heights `6, 3, 9, 6, 15, 17, 13, 13, 29`. -/
def pool6 : List (ℕ × List (ℕ × ℕ) × ℕ) :=
  [(7, [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)], 6),
   (19, [(0, 1), (2, 0), (4, 2), (5, 1), (6, 0), (8, 2), (10, 1), (11, 0), (14, 1), (15, 0)], 3),
   (31, [(0, 8), (2, 7), (4, 6), (6, 5), (7, 3), (9, 2), (11, 1), (13, 0), (16, 7), (18, 6), (20,
     5), (22, 4), (24, 3), (26, 2), (28, 1)], 9),
   (43, [(0, 2), (2, 5), (3, 4), (6, 4), (7, 1), (12, 2), (13, 1), (16, 1), (17, 0), (19, 3), (22,
     3), (23, 0), (25, 5), (26, 1), (31, 1), (36, 3), (37, 0), (40, 2)], 6),
   (67, [(0, 5), (2, 8), (4, 14), (5, 9), (6, 1), (10, 11), (11, 2), (14, 3), (16, 3), (18, 12),
     (24, 4), (25, 1), (27, 7), (32, 10), (34, 0), (36, 0), (42, 6), (44, 13), (53, 12), (55,
     12), (63, 13), (64, 3), (65, 0)], 15),
   (79, [(0, 9), (2, 12), (5, 1), (7, 4), (8, 1), (14, 16), (19, 13), (20, 11), (22, 8), (24, 5),
     (25, 2), (30, 0), (36, 14), (37, 12), (39, 15), (42, 3), (44, 7), (45, 1), (49, 13), (56,
     16), (58, 10), (61, 14), (62, 2), (65, 6), (67, 0), (74, 3), (78, 15)], 17),
   (103, [(0, 4), (2, 8), (4, 8), (7, 12), (8, 0), (11, 7), (13, 3), (15, 0), (18, 7), (19, 6),
     (20, 0), (25, 1), (30, 1), (35, 9), (36, 0), (40, 8), (47, 2), (51, 5), (52, 4), (57, 10),
     (62, 10), (63, 1), (67, 11), (68, 0), (78, 6), (83, 5), (85, 2), (88, 11), (90, 6), (95,
     5)], 13),
   (127, [(0, 12), (2, 9), (6, 3), (9, 5), (19, 6), (21, 1), (24, 12), (26, 11), (28, 4), (32, 3),
     (43, 10), (45, 1), (47, 0), (50, 11), (52, 8), (58, 10), (62, 9), (65, 10), (69, 4), (71,
     0), (81, 1), (84, 7), (86, 6), (88, 1), (91, 11), (93, 2), (98, 11), (99, 7), (100, 0),
     (107, 0), (110, 10), (114, 7), (122, 2)], 13),
   (139, [(0, 14), (6, 13), (7, 0), (18, 19), (24, 11), (25, 6), (27, 17), (31, 5), (33, 16), (38,
     25), (39, 15), (42, 0), (44, 2), (47, 23), (49, 28), (54, 18), (58, 7), (66, 20), (67, 3),
     (74, 24), (79, 10), (85, 9), (91, 8), (93, 21), (96, 0), (104, 3), (110, 1), (117, 17),
     (118, 12), (120, 26), (126, 22), (128, 27), (135, 1), (137, 4)], 29)]

end KthPower
