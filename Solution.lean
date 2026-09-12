import RK.Main

/-!
# Sets of integers with no k-th-power difference: the directed construction

The ten statements of `Challenge.lean`, restated verbatim and discharged from `RK.Main`.
The definitions they mention — `IsNonzeroPowerMod`, `diffMod`, `ValidRankedSupport`,
`ValidPool`, `alpha`, `PowerDifferenceFree`, `D`, `pool4`, `pool6` — are the ones of
`RK.Defs`, again verbatim. This file does not import `Challenge.lean`.
-/

namespace KthPower

/-- **The directed construction at every `k`, liminf form.** For `k ≥ 2` and every pool `P`
for `k`, `alpha k P ≤ liminf log D_k(N) / log N`. -/
theorem directed_liminf (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) :
    alpha k P ≤ Filter.liminf (fun N : ℕ => Real.log (D k N) / Real.log N) Filter.atTop := by
  exact directed_liminf_internal k hk P hP

/-- **The directed construction at every `k`, pointwise form.** For `k ≥ 2`, every pool `P` for
`k` and every `ρ < alpha k P`, `N ^ ρ ≤ D_k(N)` for all sufficiently large `N`. -/
theorem directed_pointwise (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  exact directed_pointwise_internal k hk P hP ρ hρ

/-- The list `pool4` is a pool for `k = 4`. -/
theorem pool4_valid : ValidPool 4 pool4 := by
  exact pool4_valid_internal

/-- The list `pool6` is a pool for `k = 6`. -/
theorem pool6_valid : ValidPool 6 pool6 := by
  exact pool6_valid_internal

/-- The exponent at `k = 4` exceeds the transfer value `(3 + log 6 / log 17) / 4 = 0.908103…`
obtained from the six fourth-power-difference-free residues modulo `17`. -/
theorem alpha4_gt_transfer : (3 + Real.log 6 / Real.log 17) / 4 < alpha 4 pool4 := by
  exact alpha4_gt_transfer_internal

/-- A decimal lower bound for the exponent at `k = 4` (its value is `0.910358…`). -/
theorem alpha4_gt : (0.9103 : ℝ) < alpha 4 pool4 := by
  exact alpha4_gt_internal

/-- The exponent at `k = 6` exceeds the transfer value `(5 + log 6 / log 13) / 6 = 0.949759…`
obtained from the six sixth-power-difference-free residues modulo `13`. -/
theorem alpha6_gt_transfer : (5 + Real.log 6 / Real.log 13) / 6 < alpha 6 pool6 := by
  exact alpha6_gt_transfer_internal

/-- A decimal lower bound for the exponent at `k = 6` (its value is `0.950739…`). -/
theorem alpha6_gt : (0.9507 : ℝ) < alpha 6 pool6 := by
  exact alpha6_gt_internal

/-- **Fourth powers:** `alpha 4 pool4 ≤ liminf log D_4(N) / log N`. -/
theorem fourth_power_liminf :
    alpha 4 pool4 ≤ Filter.liminf (fun N : ℕ => Real.log (D 4 N) / Real.log N) Filter.atTop := by
  exact fourth_power_liminf_internal

/-- **Sixth powers:** `alpha 6 pool6 ≤ liminf log D_6(N) / log N`. -/
theorem sixth_power_liminf :
    alpha 6 pool6 ≤ Filter.liminf (fun N : ℕ => Real.log (D 6 N) / Real.log N) Filter.atTop := by
  exact sixth_power_liminf_internal

end KthPower
