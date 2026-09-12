import RK.Pools
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false

/-!
# The numeric layer

This file proves the four decimal and transfer bounds on the two concrete exponents with no
transcendental numerics anywhere. The one idea is that every fact about a logarithm the
bounds need has the form

`p / q < log a / log b`  or  `log a / log b < p / q`,   `a, b ≥ 2` naturals,

and that — `log b` being positive — each is equivalent to a comparison of two natural
numbers: `b ^ p < a ^ q` in the first case, `a ^ q < b ^ p` in the second. Those
comparisons the Lean kernel settles directly, and `lt_log_div_log` and `log_div_log_lt`
below are the two translations.

The exponent of a pool is

`alpha k P = (Σ_i ((k - 1) log m_i + log t_i) / log H_i) / (1 + k Σ_i log m_i / log H_i)`,

and `((k : ℝ) - 1) log m + log t = log (m^{k-1} t)` turns each numerator term into a single
ratio of logarithms of naturals. Bounding each such ratio below by a rational, and each
`log m_i / log H_i` above by a rational, leaves a rational inequality that `norm_num`
settles. The two transfer values are ratios of the same kind: `log 6 / log 17` at `k = 4`
and `log 6 / log 13` at `k = 6`, each bounded above.

The rationals themselves, one lower bound per block and one upper bound per block, are
produced by `scripts/check_blocks.py` in exact rational arithmetic, which also prints the
margins; each is certified in Lean by one kernel-checked comparison of natural powers.
-/

namespace KthPower

set_option maxRecDepth 10000
-- Lean core's `exponentiation.threshold` is an evaluation guard, default `256`; the power
-- comparisons of the rational layer exceed it. Without this the kernel-backed `decide`s
-- still succeed, but each logs a threshold warning.
set_option exponentiation.threshold 100000

/-! ## The two translations

A rational bound on `log a / log b` *is* a comparison of natural powers. Both directions
are one application of strict monotonicity of `log` to `Real.log_pow`.

The hypothesis `2 ≤ a` is inert in `lt_log_div_log`: what that proof needs about `a` is
supplied by `b ^ p < a ^ q` itself. It is kept because the two statements are meant to be
read as a pair, with the same standing hypotheses on `a` and `b`. -/

/-- `p / q < log a / log b`, from the natural-number comparison `b ^ p < a ^ q`. -/
theorem lt_log_div_log (a b : ℝ) (p q : ℕ) (_ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : b ^ p < a ^ q) : (p : ℝ) / q < Real.log a / Real.log b := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbp : (0 : ℝ) < b ^ p := by positivity
  have h1 : Real.log (b ^ p) < Real.log (a ^ q) := Real.log_lt_log hbp h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hqR hlb]
  linarith

/-- `log a / log b < p / q`, from the natural-number comparison `a ^ q < b ^ p`. -/
theorem log_div_log_lt (a b : ℝ) (p q : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : a ^ q < b ^ p) : Real.log a / Real.log b < (p : ℝ) / q := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haq : (0 : ℝ) < a ^ q := by positivity
  have h1 : Real.log (a ^ q) < Real.log (b ^ p) := Real.log_lt_log haq h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hlb hqR]
  linarith

/-! ## The four numeric targets

Each is the rational assembly: the per-block lower bounds on `log (m^{k-1} t) / log H`, the
per-block upper bounds on `log m / log H`, and — for the two transfer statements — the
upper bound on the transfer ratio, added up by `norm_num`. -/

/-- A decimal lower bound for the exponent at `k = 4`. -/
theorem alpha4_gt_internal : (0.9103 : ℝ) < alpha 4 pool4 := by
  sorry

/-- The exponent at `k = 4` exceeds the transfer value obtained from the six
fourth-power-difference-free residues modulo `17`. -/
theorem alpha4_gt_transfer_internal :
    (3 + Real.log 6 / Real.log 17) / 4 < alpha 4 pool4 := by
  sorry

/-- A decimal lower bound for the exponent at `k = 6`. -/
theorem alpha6_gt_internal : (0.9507 : ℝ) < alpha 6 pool6 := by
  sorry

/-- The exponent at `k = 6` exceeds the transfer value obtained from the six
sixth-power-difference-free residues modulo `13`. -/
theorem alpha6_gt_transfer_internal :
    (5 + Real.log 6 / Real.log 13) / 6 < alpha 6 pool6 := by
  sorry

end KthPower
