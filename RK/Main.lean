import RK.Asymptotics
import RK.Pools
import RK.Numeric

set_option linter.unusedVariables false

/-!
# The ten targets

Everything here is glue. The two general theorems are the internal statements of
`RK.Asymptotics`; the two pool validities are `RK.Pools`; the four numeric bounds are
`RK.Numeric`; and the two instances are the general liminf theorem applied to the two
pools.

The names of `Challenge.lean` are left free: `Solution.lean` declares them, with the
`_internal` theorems below as their proofs.
-/

namespace KthPower

/-- **The directed construction at every `k`, liminf form.** For `k ≥ 2` and every pool `P`
for `k`, `alpha k P ≤ liminf log D_k(N) / log N`. -/
theorem directed_liminf_internal (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) :
    alpha k P ≤ Filter.liminf (fun N : ℕ => Real.log (D k N) / Real.log N) Filter.atTop :=
  liminf_internal k hk P hP

/-- **The directed construction at every `k`, pointwise form.** For `k ≥ 2`, every pool `P`
for `k` and every `ρ < alpha k P`, `N ^ ρ ≤ D_k(N)` for all sufficiently large `N`. -/
theorem directed_pointwise_internal (k : ℕ) (hk : 2 ≤ k) (P : List (ℕ × List (ℕ × ℕ) × ℕ))
    (hP : ValidPool k P) (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) :=
  pointwise_internal k hk P hP ρ hρ

/-- **Fourth powers:** the general theorem at `pool4`. -/
theorem fourth_power_liminf_internal :
    alpha 4 pool4 ≤ Filter.liminf (fun N : ℕ => Real.log (D 4 N) / Real.log N) Filter.atTop :=
  directed_liminf_internal 4 (by norm_num) pool4 pool4_valid_internal

/-- **Sixth powers:** the general theorem at `pool6`. -/
theorem sixth_power_liminf_internal :
    alpha 6 pool6 ≤ Filter.liminf (fun N : ℕ => Real.log (D 6 N) / Real.log N) Filter.atTop :=
  directed_liminf_internal 6 (by norm_num) pool6 pool6_valid_internal

end KthPower
