import RK.Pools

/-!
# The two exponents, bounded below without transcendental arithmetic

`alpha k P` is a ratio of sums of ratios of logarithms. This file proves the four numeric claims
about its two concrete values — that `alpha 4 pool4` exceeds `0.9103` and the transfer value
`(3 + log 6 / log 17) / 4`, and that `alpha 6 pool6` exceeds `0.9507` and the transfer value
`(5 + log 6 / log 13) / 6` — with no floating-point or interval arithmetic anywhere.

The one idea is that every fact about a logarithm needed here has the form

`p / q < log a / log b`  or  `log a / log b < p / q`,   `a, b ≥ 2` naturals,

and that — `log b` being positive — each is equivalent to a comparison of two natural numbers:
`b ^ p < a ^ q` in the first case, `a ^ q < b ^ p` in the second. The Lean kernel settles such a
comparison directly, on numbers of a few thousand digits, in milliseconds; `lt_log_div_log` and
`log_div_log_lt` are the two translations, and the rest of the file is those two applied
thirty-six times and the resulting rationals added up in exact arithmetic.

## The shape of the bound

For a pool `P` with blocks `(m, sup, H)` and `t = sup.length`,

`alpha k P = (Σ log (m ^ (k-1) t) / log H) / (1 + k Σ log m / log H)`,

so a lower bound for `alpha` needs a lower bound `ρ` for each numerator ratio and an upper bound
`σ` for each `log m / log H`. `alpha4_eq` and `alpha6_eq` put `alpha` in exactly that form, using
`(k - 1) log m + log t = log (m ^ (k-1) t)` block by block; the seventeen `logNum…` lemmas are
those identities. Then `alpha ≥ (Σ ρ) / (1 + k Σ σ)`, a rational number, and the two core
theorems `alpha4_gt_rational` and `alpha6_gt_rational` state what that rational clears.

## The rationals

Each `p / q` below is a best rational approximation to the ratio it bounds with denominator at
most `400`. Every one was checked twice before being written here — against the true ratio in
high-precision arithmetic, and as an exact integer comparison `b ^ p < a ^ q` — and
`scripts/check_blocks.py` reruns both checks, and the rational assembly, from the pools alone.
The assembled bounds are

`alpha 4 pool4 > 0.910334755826…`  against a true value of `0.910358021…`, and
`alpha 6 pool6 > 0.950714529769…`  against a true value of `0.950738856…`,

so the roundings cost `2.3 × 10⁻⁵` of the `5.8 × 10⁻⁵` available above `0.9103` and `2.4 × 10⁻⁵`
of the `3.9 × 10⁻⁵` available above `0.9507`; the decimal targets clear with margins
`3.5 × 10⁻⁵` and `1.5 × 10⁻⁵`, and the transfer values, which sit `2.3 × 10⁻³` and `1.0 × 10⁻³`
below the exponents, clear far more comfortably. Every numeral in the `ρ` and `σ` sections is
substitutable: tightening a bound means replacing four numbers on one line, since each lemma is
one application of a translation lemma plus one kernel comparison.

## Why `decide` on the power comparisons

A comparison of two natural-number literals *is* a kernel computation, and `decide` is what hands
it to the kernel's arbitrary-precision arithmetic directly: `Nat.pow` and `Nat.decLt` on the
numerals, nothing else. The largest pair here — `29 ^ 2931`, of `4287` digits, against
`1764220719766 ^ 350` — costs milliseconds that way, and all thirty-six comparisons together are
a small part of this file's elaboration. Since `decide` is more kernel-bound than `norm_num`, not
less, this strengthens the trust posture rather than relaxing it; `norm_num` and `linarith` are
left the purely rational assembly at the end, where the numbers are small.
-/

namespace KthPower

set_option maxRecDepth 10000
-- Lean core's `exponentiation.threshold` is an evaluation guard, default `256`; the comparisons
-- below exceed it. Without this the kernel-backed `decide`s still succeed, but each logs a
-- threshold warning. The proof terms are kernel-checked either way.
set_option exponentiation.threshold 100000

/-! ## The two translations

A rational bound on `log a / log b` *is* a comparison of natural powers. Both directions are one
application of strict monotonicity of `log` to `Real.log_pow`.

The hypothesis `2 ≤ a` is inert in `lt_log_div_log`: what that proof needs about `a` is supplied
by `b ^ p < a ^ q` itself. It is kept because the two statements are meant to be read as a pair,
with the same standing hypotheses on `a` and `b`, and because every caller has it to hand. -/

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

/-! ## The block numerators

`(k - 1) log m + log t = log (m ^ (k-1) t)`: seventeen instances, one per block, so that each
numerator ratio is a single `log a / log b` and the translation lemmas apply to it. -/

/-- The numerator of the block at `m = 5`, `k = 4`: `5 ^ 3 · 4 = 500`. -/
theorem logNum4_5 : Real.log 500 = 3 * Real.log 5 + Real.log 4 := by
  rw [show (500 : ℝ) = 5 ^ (3 : ℕ) * 4 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 13`, `k = 4`: `13 ^ 3 · 7 = 15379`. -/
theorem logNum4_13 : Real.log 15379 = 3 * Real.log 13 + Real.log 7 := by
  rw [show (15379 : ℝ) = 13 ^ (3 : ℕ) * 7 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 29`, `k = 4`: `29 ^ 3 · 12 = 292668`. -/
theorem logNum4_29 : Real.log 292668 = 3 * Real.log 29 + Real.log 12 := by
  rw [show (292668 : ℝ) = 29 ^ (3 : ℕ) * 12 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 37`, `k = 4`: `37 ^ 3 · 13 = 658489`. -/
theorem logNum4_37 : Real.log 658489 = 3 * Real.log 37 + Real.log 13 := by
  rw [show (658489 : ℝ) = 37 ^ (3 : ℕ) * 13 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 53`, `k = 4`: `53 ^ 3 · 16 = 2382032`. -/
theorem logNum4_53 : Real.log 2382032 = 3 * Real.log 53 + Real.log 16 := by
  rw [show (2382032 : ℝ) = 53 ^ (3 : ℕ) * 16 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 61`, `k = 4`: `61 ^ 3 · 16 = 3631696`. -/
theorem logNum4_61 : Real.log 3631696 = 3 * Real.log 61 + Real.log 16 := by
  rw [show (3631696 : ℝ) = 61 ^ (3 : ℕ) * 16 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 101`, `k = 4`: `101 ^ 3 · 20 = 20606020`. -/
theorem logNum4_101 : Real.log 20606020 = 3 * Real.log 101 + Real.log 20 := by
  rw [show (20606020 : ℝ) = 101 ^ (3 : ℕ) * 20 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 109`, `k = 4`: `109 ^ 3 · 21 = 27195609`. -/
theorem logNum4_109 : Real.log 27195609 = 3 * Real.log 109 + Real.log 21 := by
  rw [show (27195609 : ℝ) = 109 ^ (3 : ℕ) * 21 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 7`, `k = 6`: `7 ^ 5 · 6 = 100842`. -/
theorem logNum6_7 : Real.log 100842 = 5 * Real.log 7 + Real.log 6 := by
  rw [show (100842 : ℝ) = 7 ^ (5 : ℕ) * 6 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 19`, `k = 6`: `19 ^ 5 · 10 = 24760990`. -/
theorem logNum6_19 : Real.log 24760990 = 5 * Real.log 19 + Real.log 10 := by
  rw [show (24760990 : ℝ) = 19 ^ (5 : ℕ) * 10 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 31`, `k = 6`: `31 ^ 5 · 15 = 429437265`. -/
theorem logNum6_31 : Real.log 429437265 = 5 * Real.log 31 + Real.log 15 := by
  rw [show (429437265 : ℝ) = 31 ^ (5 : ℕ) * 15 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 43`, `k = 6`: `43 ^ 5 · 18 = 2646151974`. -/
theorem logNum6_43 : Real.log 2646151974 = 5 * Real.log 43 + Real.log 18 := by
  rw [show (2646151974 : ℝ) = 43 ^ (5 : ℕ) * 18 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 67`, `k = 6`: `67 ^ 5 · 23 = 31052877461`. -/
theorem logNum6_67 : Real.log 31052877461 = 5 * Real.log 67 + Real.log 23 := by
  rw [show (31052877461 : ℝ) = 67 ^ (5 : ℕ) * 23 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 79`, `k = 6`: `79 ^ 5 · 27 = 83080522773`. -/
theorem logNum6_79 : Real.log 83080522773 = 5 * Real.log 79 + Real.log 27 := by
  rw [show (83080522773 : ℝ) = 79 ^ (5 : ℕ) * 27 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 103`, `k = 6`: `103 ^ 5 · 30 = 347782222290`. -/
theorem logNum6_103 : Real.log 347782222290 = 5 * Real.log 103 + Real.log 30 := by
  rw [show (347782222290 : ℝ) = 103 ^ (5 : ℕ) * 30 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 127`, `k = 6`: `127 ^ 5 · 33 = 1090266190431`. -/
theorem logNum6_127 : Real.log 1090266190431 = 5 * Real.log 127 + Real.log 33 := by
  rw [show (1090266190431 : ℝ) = 127 ^ (5 : ℕ) * 33 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- The numerator of the block at `m = 139`, `k = 6`: `139 ^ 5 · 34 = 1764220719766`. -/
theorem logNum6_139 : Real.log 1764220719766 = 5 * Real.log 139 + Real.log 34 := by
  rw [show (1764220719766 : ℝ) = 139 ^ (5 : ℕ) * 34 by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-! ## The two exponents as expressions in numerals

Unfolding the pool folds, once, is what lets the rest of the file speak in numerals. -/

/-- `alpha 4 pool4`, with the `pool4` fold evaluated and each block numerator merged into a
single logarithm. -/
theorem alpha4_eq :
    alpha 4 pool4 =
      (Real.log 500 / Real.log 4 + Real.log 15379 / Real.log 4 + Real.log 292668 / Real.log 11 +
        Real.log 658489 / Real.log 11 + Real.log 2382032 / Real.log 8 +
        Real.log 3631696 / Real.log 10 + Real.log 20606020 / Real.log 12 +
        Real.log 27195609 / Real.log 8) /
      (1 + 4 * (Real.log 5 / Real.log 4 + Real.log 13 / Real.log 4 + Real.log 29 / Real.log 11 +
        Real.log 37 / Real.log 11 + Real.log 53 / Real.log 8 + Real.log 61 / Real.log 10 +
        Real.log 101 / Real.log 12 + Real.log 109 / Real.log 8)) := by
  rw [logNum4_5, logNum4_13, logNum4_29, logNum4_37, logNum4_53, logNum4_61, logNum4_101,
    logNum4_109]
  norm_num [alpha, pool4]
  ring

/-- `alpha 6 pool6`, with the `pool6` fold evaluated and each block numerator merged into a
single logarithm. -/
theorem alpha6_eq :
    alpha 6 pool6 =
      (Real.log 100842 / Real.log 6 + Real.log 24760990 / Real.log 3 +
        Real.log 429437265 / Real.log 9 + Real.log 2646151974 / Real.log 6 +
        Real.log 31052877461 / Real.log 15 + Real.log 83080522773 / Real.log 17 +
        Real.log 347782222290 / Real.log 13 + Real.log 1090266190431 / Real.log 13 +
        Real.log 1764220719766 / Real.log 29) /
      (1 + 6 * (Real.log 7 / Real.log 6 + Real.log 19 / Real.log 3 + Real.log 31 / Real.log 9 +
        Real.log 43 / Real.log 6 + Real.log 67 / Real.log 15 + Real.log 79 / Real.log 17 +
        Real.log 103 / Real.log 13 + Real.log 127 / Real.log 13 +
        Real.log 139 / Real.log 29)) := by
  rw [logNum6_7, logNum6_19, logNum6_31, logNum6_43, logNum6_67, logNum6_79, logNum6_103,
    logNum6_127, logNum6_139]
  norm_num [alpha, pool6]
  ring

/-! ## The eight lower bounds `ρ` at `k = 4`

**Substitutable numerals.** Each line is `lt_log_div_log (m ^ 3 t) H p q … (H ^ p < (m ^ 3 t) ^ q)`;
replacing `p` and `q` in the statement and in the `decide`d comparison is the whole of a
retuning. -/

theorem logLo4_5 : (1179 : ℝ) / 263 < Real.log 500 / Real.log 4 :=
  lt_log_div_log 500 4 1179 263 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (4 : ℕ) ^ 1179 < 500 ^ 263))

theorem logLo4_13 : (1370 : ℝ) / 197 < Real.log 15379 / Real.log 4 :=
  lt_log_div_log 15379 4 1370 197 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (4 : ℕ) ^ 1370 < 15379 ^ 197))

theorem logLo4_29 : (1454 : ℝ) / 277 < Real.log 292668 / Real.log 11 :=
  lt_log_div_log 292668 11 1454 277 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (11 : ℕ) ^ 1454 < 292668 ^ 277))

theorem logLo4_37 : (2017 : ℝ) / 361 < Real.log 658489 / Real.log 11 :=
  lt_log_div_log 658489 11 2017 361 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (11 : ℕ) ^ 2017 < 658489 ^ 361))

theorem logLo4_53 : (346 : ℝ) / 49 < Real.log 2382032 / Real.log 8 :=
  lt_log_div_log 2382032 8 346 49 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (8 : ℕ) ^ 346 < 2382032 ^ 49))

theorem logLo4_61 : (2401 : ℝ) / 366 < Real.log 3631696 / Real.log 10 :=
  lt_log_div_log 3631696 10 2401 366 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (10 : ℕ) ^ 2401 < 3631696 ^ 366))

theorem logLo4_101 : (1735 : ℝ) / 256 < Real.log 20606020 / Real.log 12 :=
  lt_log_div_log 20606020 12 1735 256 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (12 : ℕ) ^ 1735 < 20606020 ^ 256))

theorem logLo4_109 : (2091 : ℝ) / 254 < Real.log 27195609 / Real.log 8 :=
  lt_log_div_log 27195609 8 2091 254 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (8 : ℕ) ^ 2091 < 27195609 ^ 254))

/-! ## The eight upper bounds `σ` at `k = 4`

**Substitutable numerals**, on the same terms as the section above. -/

theorem logHi4_5 : Real.log 5 / Real.log 4 < (238 : ℝ) / 205 :=
  log_div_log_lt 5 4 238 205 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (5 : ℕ) ^ 205 < 4 ^ 238))

theorem logHi4_13 : Real.log 13 / Real.log 4 < (420 : ℝ) / 227 :=
  log_div_log_lt 13 4 420 227 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (13 : ℕ) ^ 227 < 4 ^ 420))

theorem logHi4_29 : Real.log 29 / Real.log 11 < (521 : ℝ) / 371 :=
  log_div_log_lt 29 11 521 371 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (29 : ℕ) ^ 371 < 11 ^ 521))

theorem logHi4_37 : Real.log 37 / Real.log 11 < (128 : ℝ) / 85 :=
  log_div_log_lt 37 11 128 85 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (37 : ℕ) ^ 85 < 11 ^ 128))

theorem logHi4_53 : Real.log 53 / Real.log 8 < (758 : ℝ) / 397 :=
  log_div_log_lt 53 8 758 397 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (53 : ℕ) ^ 397 < 8 ^ 758))

theorem logHi4_61 : Real.log 61 / Real.log 10 < (341 : ℝ) / 191 :=
  log_div_log_lt 61 10 341 191 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (61 : ℕ) ^ 191 < 10 ^ 341))

theorem logHi4_101 : Real.log 101 / Real.log 12 < (743 : ℝ) / 400 :=
  log_div_log_lt 101 12 743 400 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (101 : ℕ) ^ 400 < 12 ^ 743))

theorem logHi4_109 : Real.log 109 / Real.log 8 < (837 : ℝ) / 371 :=
  log_div_log_lt 109 8 837 371 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (109 : ℕ) ^ 371 < 8 ^ 837))

/-! ## The nine lower bounds `ρ` at `k = 6` -/

theorem logLo6_7 : (1749 : ℝ) / 272 < Real.log 100842 / Real.log 6 :=
  lt_log_div_log 100842 6 1749 272 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (6 : ℕ) ^ 1749 < 100842 ^ 272))

theorem logLo6_19 : (4587 : ℝ) / 296 < Real.log 24760990 / Real.log 3 :=
  lt_log_div_log 24760990 3 4587 296 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (3 : ℕ) ^ 4587 < 24760990 ^ 296))

theorem logLo6_31 : (3284 : ℝ) / 363 < Real.log 429437265 / Real.log 9 :=
  lt_log_div_log 429437265 9 3284 363 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (9 : ℕ) ^ 3284 < 429437265 ^ 363))

theorem logLo6_43 : (1889 : ℝ) / 156 < Real.log 2646151974 / Real.log 6 :=
  lt_log_div_log 2646151974 6 1889 156 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (6 : ℕ) ^ 1889 < 2646151974 ^ 156))

theorem logLo6_67 : (2150 : ℝ) / 241 < Real.log 31052877461 / Real.log 15 :=
  lt_log_div_log 31052877461 15 2150 241 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (15 : ℕ) ^ 2150 < 31052877461 ^ 241))

theorem logLo6_79 : (1837 : ℝ) / 207 < Real.log 83080522773 / Real.log 17 :=
  lt_log_div_log 83080522773 17 1837 207 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (17 : ℕ) ^ 1837 < 83080522773 ^ 207))

theorem logLo6_103 : (1637 : ℝ) / 158 < Real.log 347782222290 / Real.log 13 :=
  lt_log_div_log 347782222290 13 1637 158 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (13 : ℕ) ^ 1637 < 347782222290 ^ 158))

theorem logLo6_127 : (3123 : ℝ) / 289 < Real.log 1090266190431 / Real.log 13 :=
  lt_log_div_log 1090266190431 13 3123 289 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (13 : ℕ) ^ 3123 < 1090266190431 ^ 289))

theorem logLo6_139 : (2931 : ℝ) / 350 < Real.log 1764220719766 / Real.log 29 :=
  lt_log_div_log 1764220719766 29 2931 350 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (29 : ℕ) ^ 2931 < 1764220719766 ^ 350))

/-! ## The nine upper bounds `σ` at `k = 6` -/

theorem logHi6_7 : Real.log 7 / Real.log 6 < (366 : ℝ) / 337 :=
  log_div_log_lt 7 6 366 337 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (7 : ℕ) ^ 337 < 6 ^ 366))

theorem logHi6_19 : Real.log 19 / Real.log 3 < (729 : ℝ) / 272 :=
  log_div_log_lt 19 3 729 272 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (19 : ℕ) ^ 272 < 3 ^ 729))

theorem logHi6_31 : Real.log 31 / Real.log 9 < (497 : ℝ) / 318 :=
  log_div_log_lt 31 9 497 318 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (31 : ℕ) ^ 318 < 9 ^ 497))

theorem logHi6_43 : Real.log 43 / Real.log 6 < (254 : ℝ) / 121 :=
  log_div_log_lt 43 6 254 121 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (43 : ℕ) ^ 121 < 6 ^ 254))

theorem logHi6_67 : Real.log 67 / Real.log 15 < (604 : ℝ) / 389 :=
  log_div_log_lt 67 15 604 389 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (67 : ℕ) ^ 389 < 15 ^ 604))

theorem logHi6_79 : Real.log 79 / Real.log 17 < (566 : ℝ) / 367 :=
  log_div_log_lt 79 17 566 367 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (79 : ℕ) ^ 367 < 17 ^ 566))

theorem logHi6_103 : Real.log 103 / Real.log 13 < (468 : ℝ) / 259 :=
  log_div_log_lt 103 13 468 259 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (103 : ℕ) ^ 259 < 13 ^ 468))

theorem logHi6_127 : Real.log 127 / Real.log 13 < (17 : ℝ) / 9 :=
  log_div_log_lt 127 13 17 9 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (127 : ℕ) ^ 9 < 13 ^ 17))

theorem logHi6_139 : Real.log 139 / Real.log 29 < (551 : ℝ) / 376 :=
  log_div_log_lt 139 29 551 376 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (139 : ℕ) ^ 376 < 29 ^ 551))

/-! ## The two transfer values

Ruzsa's transfer from a k-th-power-difference-free set of `r` residues modulo a square-free `m`
gives the exponent `(k - 1 + log_m r) / k`. The two comparisons this file makes are against the
six residues modulo `17` at `k = 4` and the six modulo `13` at `k = 6`, so the values to exceed are
`(3 + log 6 / log 17) / 4` and `(5 + log 6 / log 13) / 6`, and an upper bound on each `log 6 /
log H` is what the comparison needs. -/

/-- The transfer value at `k = 4` is below `(3 + 117/185) / 4 = 0.908108…`. -/
theorem logHi_transfer4 : Real.log 6 / Real.log 17 < (117 : ℝ) / 185 :=
  log_div_log_lt 6 17 117 185 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (6 : ℕ) ^ 185 < 17 ^ 117))

/-- The transfer value at `k = 6` is below `(5 + 146/209) / 6 = 0.949760…`. -/
theorem logHi_transfer6 : Real.log 6 / Real.log 13 < (146 : ℝ) / 209 :=
  log_div_log_lt 6 13 146 209 (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by decide : (6 : ℕ) ^ 209 < 13 ^ 146))

/-! ## The assembly

`(Σ ρ) / (1 + k Σ σ)` is a rational number below the exponent, and the passage from the bounds to
that inequality needs only that the denominator is positive, which every `log H > 0` supplies.
The exact assembled values are `0.910334755826…` and `0.950714529769…`; the two theorems below
state a decimal just underneath each of them, `0.91033` and `0.95071`, and the four target
statements follow from those two by rational arithmetic alone. -/

/-- **The exponent at `k = 4` exceeds `0.91033`**, from the sixteen rational bounds on its
blocks. This is the one inequality from which both `k = 4` targets follow. -/
theorem alpha4_gt_rational : (0.91033 : ℝ) < alpha 4 pool4 := by
  have l4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have l8 : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
  have l10 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have l11 : (0 : ℝ) < Real.log 11 := Real.log_pos (by norm_num)
  have l12 : (0 : ℝ) < Real.log 12 := Real.log_pos (by norm_num)
  have d1 : (0 : ℝ) < Real.log 5 / Real.log 4 := div_pos (Real.log_pos (by norm_num)) l4
  have d2 : (0 : ℝ) < Real.log 13 / Real.log 4 := div_pos (Real.log_pos (by norm_num)) l4
  have d3 : (0 : ℝ) < Real.log 29 / Real.log 11 := div_pos (Real.log_pos (by norm_num)) l11
  have d4 : (0 : ℝ) < Real.log 37 / Real.log 11 := div_pos (Real.log_pos (by norm_num)) l11
  have d5 : (0 : ℝ) < Real.log 53 / Real.log 8 := div_pos (Real.log_pos (by norm_num)) l8
  have d6 : (0 : ℝ) < Real.log 61 / Real.log 10 := div_pos (Real.log_pos (by norm_num)) l10
  have d7 : (0 : ℝ) < Real.log 101 / Real.log 12 := div_pos (Real.log_pos (by norm_num)) l12
  have d8 : (0 : ℝ) < Real.log 109 / Real.log 8 := div_pos (Real.log_pos (by norm_num)) l8
  have hden : (0 : ℝ) <
      1 + 4 * (Real.log 5 / Real.log 4 + Real.log 13 / Real.log 4 + Real.log 29 / Real.log 11 +
        Real.log 37 / Real.log 11 + Real.log 53 / Real.log 8 + Real.log 61 / Real.log 10 +
        Real.log 101 / Real.log 12 + Real.log 109 / Real.log 8) := by linarith
  rw [alpha4_eq, lt_div_iff₀ hden]
  linarith [logLo4_5, logLo4_13, logLo4_29, logLo4_37, logLo4_53, logLo4_61, logLo4_101,
    logLo4_109, logHi4_5, logHi4_13, logHi4_29, logHi4_37, logHi4_53, logHi4_61, logHi4_101,
    logHi4_109]

/-- **The exponent at `k = 6` exceeds `0.95071`**, from the eighteen rational bounds on its
blocks. This is the one inequality from which both `k = 6` targets follow. -/
theorem alpha6_gt_rational : (0.95071 : ℝ) < alpha 6 pool6 := by
  have l3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have l6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have l9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have l13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  have l15 : (0 : ℝ) < Real.log 15 := Real.log_pos (by norm_num)
  have l17 : (0 : ℝ) < Real.log 17 := Real.log_pos (by norm_num)
  have l29 : (0 : ℝ) < Real.log 29 := Real.log_pos (by norm_num)
  have d1 : (0 : ℝ) < Real.log 7 / Real.log 6 := div_pos (Real.log_pos (by norm_num)) l6
  have d2 : (0 : ℝ) < Real.log 19 / Real.log 3 := div_pos (Real.log_pos (by norm_num)) l3
  have d3 : (0 : ℝ) < Real.log 31 / Real.log 9 := div_pos (Real.log_pos (by norm_num)) l9
  have d4 : (0 : ℝ) < Real.log 43 / Real.log 6 := div_pos (Real.log_pos (by norm_num)) l6
  have d5 : (0 : ℝ) < Real.log 67 / Real.log 15 := div_pos (Real.log_pos (by norm_num)) l15
  have d6 : (0 : ℝ) < Real.log 79 / Real.log 17 := div_pos (Real.log_pos (by norm_num)) l17
  have d7 : (0 : ℝ) < Real.log 103 / Real.log 13 := div_pos (Real.log_pos (by norm_num)) l13
  have d8 : (0 : ℝ) < Real.log 127 / Real.log 13 := div_pos (Real.log_pos (by norm_num)) l13
  have d9 : (0 : ℝ) < Real.log 139 / Real.log 29 := div_pos (Real.log_pos (by norm_num)) l29
  have hden : (0 : ℝ) <
      1 + 6 * (Real.log 7 / Real.log 6 + Real.log 19 / Real.log 3 + Real.log 31 / Real.log 9 +
        Real.log 43 / Real.log 6 + Real.log 67 / Real.log 15 + Real.log 79 / Real.log 17 +
        Real.log 103 / Real.log 13 + Real.log 127 / Real.log 13 +
        Real.log 139 / Real.log 29) := by linarith
  rw [alpha6_eq, lt_div_iff₀ hden]
  linarith [logLo6_7, logLo6_19, logLo6_31, logLo6_43, logLo6_67, logLo6_79, logLo6_103,
    logLo6_127, logLo6_139, logHi6_7, logHi6_19, logHi6_31, logHi6_43, logHi6_67, logHi6_79,
    logHi6_103, logHi6_127, logHi6_139]

/-- **A decimal lower bound at `k = 4`:** `0.9103 < alpha 4 pool4` (the true value is
`0.910358…`). -/
theorem alpha4_gt_internal : (0.9103 : ℝ) < alpha 4 pool4 :=
  lt_trans (by norm_num) alpha4_gt_rational

/-- **The exponent at `k = 4` exceeds the transfer value** `(3 + log 6 / log 17) / 4 =
0.908103119…`, the exponent Ruzsa's transfer gives from the six fourth-power-difference-free
residues modulo `17`. -/
theorem alpha4_gt_transfer_internal :
    (3 + Real.log 6 / Real.log 17) / 4 < alpha 4 pool4 := by
  have h : (3 + Real.log 6 / Real.log 17) / 4 < (0.91033 : ℝ) := by linarith [logHi_transfer4]
  exact h.trans alpha4_gt_rational

/-- **A decimal lower bound at `k = 6`:** `0.9507 < alpha 6 pool6` (the true value is
`0.950739…`). -/
theorem alpha6_gt_internal : (0.9507 : ℝ) < alpha 6 pool6 :=
  lt_trans (by norm_num) alpha6_gt_rational

/-- **The exponent at `k = 6` exceeds the transfer value** `(5 + log 6 / log 13) / 6 =
0.949759249…`, the exponent Ruzsa's transfer gives from the six sixth-power-difference-free
residues modulo `13`. -/
theorem alpha6_gt_transfer_internal :
    (5 + Real.log 6 / Real.log 13) / 6 < alpha 6 pool6 := by
  have h : (5 + Real.log 6 / Real.log 13) / 6 < (0.95071 : ℝ) := by linarith [logHi_transfer6]
  exact h.trans alpha6_gt_rational

end KthPower
