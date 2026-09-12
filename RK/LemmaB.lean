import RK.LemmaA

set_option linter.unusedVariables false

/-!
# Lemma B — from a ranked block to a set of integers with no k-th-power difference

A ranked block `C` on `Z/PZ` with `P` a perfect k-th power and a ranking of height `H`
produces, for every `L ≥ 1`, a k-th-power-difference-free set
`A_L ⊆ {1, …, (P H)^L}` with `|A_L| = |C|^L`.

The headline is the triple `lemmaB_pdf`, `integerSet_subset`, `integerSet_card`; the link
to the counting function, `le_D_of_pdf`, is at the bottom, and `lemmaB_card_le_D` packages
all four into the one inequality the exponent arithmetic consumes.

Everything between is the step spine, one named lemma per move of the argument:

| Lean | step |
| --- | --- |
| `exists_least_digit_ne_of_lt` | the least base-`P` position where `X`, `Y` differ |
| `diffMod_unique` | the reduction mod `P^L`: `z^k ≡ Y - X` |
| `word_step0_exact_dvd` | `Y - X = P^j(δ + P Z)`, i.e. `P^j` divides exactly |
| `word_step1_leading_digit` | `δ = y_j - x_j`, no borrows from below `j` |
| `word_step2_pow_dvd_pow` | `P^j` divides both `Y - X` and `P^L`, hence `P^j ∣ z^k` |
| `word_step3_root_split` | `(n^j)^k ∣ z^k` hence `n^j ∣ z` — `P = n^k` for *any* `n` |
| `word_step4_leading_power` | dividing by `P^j` shows `δ` is a k-th-power residue mod `P` |
| `word_step5_rank_drop` | `j` least, so the rank strictly drops |
| `word_mod_pow`, `wordEmbed_injOn` | the reductions of distinct elements are distinct |
| `integerSet_lt_of_rank_lt` | the displayed integer would be smaller, not larger |
| `wordBlock_card` | `B_L` has `|C|^L` elements |
| `wordRank_lt_pow` | `h_L ≤ H^L - 1`, the interval bookkeeping |

This is the stretch of the argument where the exponent does *less* work than in the lift.
The lift needed square-freeness of `m` and a valuation argument to know that the valuation
of a nonzero k-th-power residue is a multiple of `k`. Here `P = n^k` makes `P^j = (n^j)^k`
a k-th power outright, so `(n^j)^k ∣ z^k` gives `n^j ∣ z` for *every* natural `n` — one
application of `Nat.pow_dvd_pow_iff`. No primality and no square-freeness enters.

There is also no odd-`k` branch. `PowerDifferenceFree` is stated additively, as
`a + z^k ∉ A` for `z > 0`, which covers both signs of a difference; the two elements of a
would-be violating pair therefore come in a fixed order, and the rank drop is read off in
that order.
-/

namespace KthPower

/-! ## Words in base `P` -/

/-- `C^L` read as a set of residues: the `X < P ^ L` whose *every* base-`P` digit below
position `L` lies in `C`.

Unlike the lifted block there are no free positions — all `L` digits are constrained —
which is why `wordBlock_card` has no factor of `P` in it. -/
def wordBlock (P L : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Finset.range (P ^ L)).filter (fun X => ∀ j < L, digit P j X ∈ C)

/-- The word rank: the base-`H` number whose digits are the ranks of the base-`P` digits of
`X`, with the *lowest* position most significant. The weight `H ^ (L - 1 - j)` at position
`j` is what makes the lexicographic comparison of `word_step5_rank_drop` work. -/
def wordRank (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, h (digit P j X) * H ^ (L - 1 - j)

/-- The set of integers the construction produces: `{X + P^L · h_L(X) : X ∈ wordBlock}`,
translated by one so that it lands in `{1, …, (P H)^L}` rather than `{0, …, (P H)^L - 1}`. -/
def integerSet (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) : Finset ℕ :=
  (wordBlock P L C).image (fun X => X + P ^ L * wordRank P L H h X + 1)

/-- Membership in the word block, unfolded. -/
theorem mem_wordBlock (P L : ℕ) (C : Finset ℕ) (X : ℕ) :
    X ∈ wordBlock P L C ↔ X < P ^ L ∧ ∀ j < L, digit P j X ∈ C := by
  simp [wordBlock, Finset.mem_filter, Finset.mem_range]

/-- Membership in the integer set, unfolded: an element is the translate of some word's
code. -/
theorem mem_integerSet (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (a : ℕ) :
    a ∈ integerSet P L H C h ↔
      ∃ X ∈ wordBlock P L C, X + P ^ L * wordRank P L H h X + 1 = a := by
  simp only [integerSet, Finset.mem_image]

/-! ## The rank as a base-`H` string -/

/-- The word rank is a base-`H` string of length `L`, hence `< H ^ L`: half of the
interval bookkeeping. -/
theorem wordRank_lt_pow (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) (hH : 0 < H)
    (hb : ∀ i < L, h (digit P i X) < H) :
    wordRank P L H h X < H ^ L :=
  sum_reflect_lt_pow H (fun i => h (digit P i X)) L hb

/-- `wordRank` split at position `j`: the digits below `j`, the digit at `j`, the tail. -/
theorem wordRank_split (P L H j : ℕ) (h : ℕ → ℕ) (X : ℕ) (hj : j < L) :
    wordRank P L H h X =
      (∑ i ∈ Finset.range j, h (digit P i X) * H ^ (L - 1 - i))
        + h (digit P j X) * H ^ (L - 1 - j)
        + ∑ i ∈ Finset.Ico (j + 1) L, h (digit P i X) * H ^ (L - 1 - i) := by
  rw [wordRank, ← Finset.sum_range_add_sum_Ico
    (fun i => h (digit P i X) * H ^ (L - 1 - i)) (Nat.succ_le_of_lt hj),
    Finset.sum_range_succ]

/-- The geometric bound behind the lexicographic step: everything strictly above position
`j` is worth less than one unit at position `j`. -/
theorem wordRank_tail_lt (P L H j : ℕ) (h : ℕ → ℕ) (X : ℕ) (hH : 0 < H) (hj : j < L)
    (hb : ∀ i < L, h (digit P i X) < H) :
    ∑ i ∈ Finset.Ico (j + 1) L, h (digit P i X) * H ^ (L - 1 - i) < H ^ (L - 1 - j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hN : L - 1 - j = L - (j + 1) := by omega
  have hcongr : ∑ i ∈ Finset.range (L - (j + 1)),
        h (digit P (j + 1 + i) X) * H ^ (L - 1 - (j + 1 + i))
      = ∑ i ∈ Finset.range (L - (j + 1)),
        h (digit P (j + 1 + i) X) * H ^ (L - (j + 1) - 1 - i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  rw [hN, hcongr]
  exact sum_reflect_lt_pow H (fun i => h (digit P (j + 1 + i) X)) (L - (j + 1))
    fun i hi => hb _ (by omega)

/-! ## The least differing position, and the bridge to the lift's modulus -/

/-- The least base-`P` position at which two distinct words below `P ^ L` differ. A wrapper
on `exists_least_digit_ne` at `e := L`, with the positions from `L` up ruled out by
`digit_eq_zero_of_lt`. -/
theorem exists_least_digit_ne_of_lt (k P L X Y : ℕ) (hk : 1 ≤ k) (hP : 2 ≤ P)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hXY : X ≠ Y) :
    ∃ j, j < L ∧ digit P j X ≠ digit P j Y ∧ ∀ i < j, digit P i X = digit P i Y := by
  have hP0 : 0 < P := by omega
  have hLkL : L ≤ k * L := by
    calc L = 1 * L := (one_mul L).symm
      _ ≤ k * L := Nat.mul_le_mul_right L hk
  have hle : P ^ L ≤ P ^ (k * L) := Nat.pow_le_pow_right hP0 hLkL
  obtain ⟨r, hrlt, hrne, hrlow⟩ :=
    exists_least_digit_ne k P L X Y hP (lt_of_lt_of_le hX hle) (lt_of_lt_of_le hY hle) hXY
  refine ⟨r, ?_, hrne, hrlow⟩
  by_contra hcon
  have hLr : L ≤ r := by omega
  have hxz : digit P r X = 0 :=
    digit_eq_zero_of_lt P r X (lt_of_lt_of_le hX (Nat.pow_le_pow_right hP0 hLr))
  have hyz : digit P r Y = 0 :=
    digit_eq_zero_of_lt P r Y (lt_of_lt_of_le hY (Nat.pow_le_pow_right hP0 hLr))
  exact hrne (by rw [hxz, hyz])

/-- The bridge that lets the lift's Steps 0 and 1 be reused at word length `L`. For words
below `P ^ L`, the difference taken modulo `P ^ L` and the difference taken modulo the
larger `P ^ N` agree modulo `P ^ L` — the two wraparound terms differ by a multiple of
`P ^ L`. Every conclusion of Steps 0 and 1 at a position `j < L` reads the difference only
modulo `P ^ (j + 1)`, and `j + 1 ≤ L`. -/
theorem diffMod_pow_mod_pow (P L N X Y : ℕ) (hP : 2 ≤ P) (hLN : L ≤ N)
    (hX : X < P ^ L) (hY : Y < P ^ L) :
    diffMod (P ^ L) X Y % P ^ L = diffMod (P ^ N) X Y % P ^ L := by
  have hP0 : 0 < P := by omega
  have hLpos : 0 < P ^ L := Nat.pow_pos hP0
  have hNpos : 0 < P ^ N := Nat.pow_pos hP0
  have hle : P ^ L ≤ P ^ N := Nat.pow_le_pow_right hP0 hLN
  obtain ⟨c, hc⟩ : P ^ L ∣ P ^ N := Nat.pow_dvd_pow P hLN
  have hmod : (X + diffMod (P ^ N) X Y) % P ^ L = Y := by
    rcases diffMod_add (P ^ N) X Y hNpos (lt_of_lt_of_le hX hle) (lt_of_lt_of_le hY hle) with
      hh | hh
    · rw [hh, Nat.mod_eq_of_lt hY]
    · rw [hh, hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hY]
  rw [Nat.mod_eq_of_lt (diffMod_lt _ X Y hLpos)]
  exact diffMod_unique (P ^ L) X Y (diffMod (P ^ N) X Y) hLpos hX hY hmod

/-- Congruence modulo `M` transfers divisibility by any divisor `d` of `M`. This is what
turns `diffMod_pow_mod_pow` into a statement about `P ^ j ∣ ·`. -/
private theorem dvd_iff_of_mod_eq (a b M d : ℕ) (hdvd : d ∣ M) (h : a % M = b % M) :
    d ∣ a ↔ d ∣ b := by
  have hd : a % d = b % d := by
    rw [← Nat.mod_mod_of_dvd a hdvd, h, Nat.mod_mod_of_dvd b hdvd]
  constructor
  · intro ha
    exact Nat.dvd_of_mod_eq_zero (by rw [← hd]; exact Nat.mod_eq_zero_of_dvd ha)
  · intro hb
    exact Nat.dvd_of_mod_eq_zero (by rw [hd]; exact Nat.mod_eq_zero_of_dvd hb)

/-! ## Step 0 — exact divisibility at the least differing position -/

/-- Step 0 at word length `L`: with `j` the least differing digit position,
`j = v_P(diffMod (P ^ L) X Y)`. -/
theorem word_step0_exact_dvd (k P L X Y j : ℕ) (hk : 1 ≤ k) (hP : 2 ≤ P) (hL : 1 ≤ L)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hj : j < L)
    (hne : digit P j X ≠ digit P j Y) (hlow : ∀ i < j, digit P i X = digit P i Y) :
    P ^ j ∣ diffMod (P ^ L) X Y ∧ ¬ P ^ (j + 1) ∣ diffMod (P ^ L) X Y := by
  have hP0 : 0 < P := by omega
  have hLkL : L ≤ k * L := by
    calc L = 1 * L := (one_mul L).symm
      _ ≤ k * L := Nat.mul_le_mul_right L hk
  have hle : P ^ L ≤ P ^ (k * L) := Nat.pow_le_pow_right hP0 hLkL
  have hbridge := diffMod_pow_mod_pow P L (k * L) X Y hP hLkL hX hY
  obtain ⟨h1, h2⟩ := step0_exact_dvd k P L X Y j hk hP hL (lt_of_lt_of_le hX hle)
    (lt_of_lt_of_le hY hle) (by omega) hne hlow
  refine ⟨?_, fun hcon => h2 ?_⟩
  · exact (dvd_iff_of_mod_eq _ _ _ _ (Nat.pow_dvd_pow P (by omega : j ≤ L)) hbridge).mpr h1
  · exact (dvd_iff_of_mod_eq _ _ _ _ (Nat.pow_dvd_pow P (by omega : j + 1 ≤ L)) hbridge).mp hcon

/-! ## Step 1 — the leading digit, without borrows -/

/-- Step 1 at word length `L`: the `j`-th digit of the difference is the difference of the
`j`-th digits, `δ = y_j - x_j`. Positions below `j` agree, so nothing borrows into `j`. -/
theorem word_step1_leading_digit (k P L X Y j : ℕ) (hk : 1 ≤ k) (hP : 2 ≤ P) (hL : 1 ≤ L)
    (hX : X < P ^ L) (hY : Y < P ^ L) (hj : j < L)
    (hlow : ∀ i < j, digit P i X = digit P i Y) :
    digit P j (diffMod (P ^ L) X Y) = diffMod P (digit P j X) (digit P j Y) := by
  have hP0 : 0 < P := by omega
  have hLkL : L ≤ k * L := by
    calc L = 1 * L := (one_mul L).symm
      _ ≤ k * L := Nat.mul_le_mul_right L hk
  have hle : P ^ L ≤ P ^ (k * L) := Nat.pow_le_pow_right hP0 hLkL
  have hbridge := diffMod_pow_mod_pow P L (k * L) X Y hP hLkL hX hY
  have hdig : digit P j (diffMod (P ^ L) X Y) = digit P j (diffMod (P ^ (k * L)) X Y) :=
    (mod_pow_eq_iff_digits_eq P L _ _ hP).mp hbridge j hj
  rw [hdig]
  exact step1_leading_digit k P L X Y j hk hP hL (lt_of_lt_of_le hX hle)
    (lt_of_lt_of_le hY hle) (by omega) hlow

/-! ## Steps 2–4 — the leading digit is a nonzero k-th-power residue mod `P` -/

/-- Step 2: `P ^ j` divides `diffMod (P ^ L) X Y` and divides `P ^ L`, so it divides
`z ^ k` as well. -/
theorem word_step2_pow_dvd_pow (k P L j z d : ℕ) (hj : j < L)
    (hd : z ^ k % P ^ L = d) (h1 : P ^ j ∣ d) :
    P ^ j ∣ z ^ k := by
  have hdvdL : P ^ j ∣ P ^ L := Nat.pow_dvd_pow P (Nat.le_of_lt hj)
  have hsplit : P ^ L * (z ^ k / P ^ L) + z ^ k % P ^ L = z ^ k := Nat.div_add_mod _ _
  rw [← hsplit, hd]
  exact Nat.dvd_add (hdvdL.mul_right _) h1

/-- Step 3: for `P = n^k` a perfect k-th power with `n` *any* natural number — no
primality, no square-freeness — `P ^ j = (n ^ j) ^ k` divides `z ^ k` exactly when
`n ^ j` divides `z`, so the k-th power splits off a factor `P ^ j`. -/
theorem word_step3_root_split (k n P j z : ℕ) (hk : 1 ≤ k) (hP : P = n ^ k)
    (hdvd : P ^ j ∣ z ^ k) : ∃ u, z ^ k = P ^ j * u ^ k := by
  subst hP
  have h1 : (n ^ j) ^ k ∣ z ^ k := by
    rw [← pow_mul, Nat.mul_comm j k, pow_mul]
    exact hdvd
  obtain ⟨u, hu⟩ := (Nat.pow_dvd_pow_iff (by omega : k ≠ 0)).mp h1
  refine ⟨u, ?_⟩
  rw [hu, mul_pow, ← pow_mul, Nat.mul_comm j k, pow_mul]

/-- Step 4: after dividing by `P ^ j`, the leading digit `δ` is congruent to `u ^ k` mod
`P` — the tail `lam * P ^ (L - j)` is a multiple of `P` because `j < L` — and it is nonzero
because `P ^ (j + 1)` does not divide the difference. So `δ` is a nonzero k-th-power
residue mod `P`. -/
theorem word_step4_leading_power (k P L j z lam u d : ℕ) (hk : 1 ≤ k) (hP : 2 ≤ P)
    (hL : 1 ≤ L) (hd : d ≠ 0) (hdlt : d < P ^ L) (hz : z ≠ 0) (hj : j < L)
    (hlam : z ^ k = d + lam * P ^ L) (hsq : z ^ k = P ^ j * u ^ k)
    (h1 : P ^ j ∣ d) (h2 : ¬ P ^ (j + 1) ∣ d) :
    IsNonzeroPowerMod k P (digit P j d) := by
  have hP0 : 0 < P := by omega
  have hp : 0 < P ^ j := Nat.pow_pos hP0
  obtain ⟨d', hd'⟩ := h1
  have hdig : digit P j d = d' % P := by
    rw [digit, hd', Nat.mul_div_cancel_left _ hp]
  have hsplit : P ^ L = P ^ j * P ^ (L - j) := by
    rw [← pow_add]; congr 1; omega
  have hkey : P ^ j * u ^ k = P ^ j * (d' + lam * P ^ (L - j)) := by
    rw [← hsq, hlam, hd', hsplit]; ring
  have hu2 : u ^ k = d' + lam * P ^ (L - j) := Nat.eq_of_mul_eq_mul_left hp hkey
  obtain ⟨c, hc⟩ : P ∣ P ^ (L - j) := dvd_pow_self P (by omega)
  have hrw : lam * (P * c) = P * (lam * c) := by ring
  have hmod : u ^ k % P = d' % P := by
    rw [hu2, hc, hrw, Nat.add_mul_mod_self_left]
  refine ⟨?_, u % P, Nat.mod_lt _ hP0, ?_⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl]
    intro hzero
    obtain ⟨c₂, hc₂⟩ : P ∣ d' := Nat.dvd_of_mod_eq_zero hzero
    exact h2 ⟨c₂, by rw [hd', hc₂, pow_succ]; ring⟩
  · rw [hdig, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.pow_mod, hmod]

/-! ## Step 5 — the rank drop -/

/-- Step 5 at word length `L`: a drop of at least one unit at position `j`, equal digits
below it, and the geometric tail bound above it give `h_L(Y) < h_L(X)`. -/
theorem word_step5_rank_drop (P L H j : ℕ) (h : ℕ → ℕ) (C : Finset ℕ) (X Y : ℕ)
    (hH : 0 < H) (hj : j < L)
    (hXC : ∀ i < L, digit P i X ∈ C) (hYC : ∀ i < L, digit P i Y ∈ C)
    (hbd : ∀ c ∈ C, h c < H)
    (hlow : ∀ i < j, digit P i X = digit P i Y)
    (hdrop : h (digit P j Y) < h (digit P j X)) :
    wordRank P L H h Y < wordRank P L H h X := by
  have hby : ∀ i < L, h (digit P i Y) < H := fun i hi => hbd _ (hYC i hi)
  have htail := wordRank_tail_lt P L H j h Y hH hj hby
  have hmul : (h (digit P j Y) + 1) * H ^ (L - 1 - j)
      ≤ h (digit P j X) * H ^ (L - 1 - j) := Nat.mul_le_mul_right _ hdrop
  have hexp : (h (digit P j Y) + 1) * H ^ (L - 1 - j)
      = h (digit P j Y) * H ^ (L - 1 - j) + H ^ (L - 1 - j) := by ring
  have hlowsum : (∑ i ∈ Finset.range j, h (digit P i X) * H ^ (L - 1 - i))
      = ∑ i ∈ Finset.range j, h (digit P i Y) * H ^ (L - 1 - i) :=
    Finset.sum_congr rfl fun i hi => by rw [hlow i (Finset.mem_range.mp hi)]
  rw [wordRank_split P L H j h X hj, wordRank_split P L H j h Y hj, hlowsum]
  omega

/-! ## The word is recoverable from its code -/

/-- The code `X + P^L h_L(X)` reduces to `X` modulo `P ^ L`: the rank term is a multiple of
`P ^ L` and `X` is below it. -/
theorem word_mod_pow (P L H : ℕ) (h : ℕ → ℕ) (X : ℕ) (hX : X < P ^ L) :
    (X + P ^ L * wordRank P L H h X) % P ^ L = X := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- Injectivity: distinct words get distinct integers. No hypothesis is needed — for
`P = 0` and `L ≥ 1` the block is empty, and otherwise `word_mod_pow` recovers the word. -/
theorem wordEmbed_injOn (P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) :
    Set.InjOn (fun X => X + P ^ L * wordRank P L H h X + 1)
      (wordBlock P L C : Set ℕ) := by
  intro X hX Y hY hXY
  simp only [Finset.mem_coe, mem_wordBlock] at hX hY
  dsimp only at hXY
  have h' : X + P ^ L * wordRank P L H h X = Y + P ^ L * wordRank P L H h Y := by omega
  calc X = (X + P ^ L * wordRank P L H h X) % P ^ L := (word_mod_pow P L H h X hX.1).symm
    _ = (Y + P ^ L * wordRank P L H h Y) % P ^ L := by rw [h']
    _ = Y := word_mod_pow P L H h Y hY.1

/-! ## Counting the words -/

/-- One digit peeled off the bottom: the last base-`P` digit must lie in `C`, and what is
left is a word of length `L` on `X / P`. -/
theorem mem_wordBlock_succ (P L : ℕ) (C : Finset ℕ) (hP : 0 < P) (X : ℕ) :
    X ∈ wordBlock P (L + 1) C ↔ X % P ∈ C ∧ X / P ∈ wordBlock P L C := by
  rw [mem_wordBlock, mem_wordBlock]
  constructor
  · rintro ⟨hlt, hdig⟩
    refine ⟨by simpa [digit] using hdig 0 (Nat.succ_pos L), ?_, ?_⟩
    · refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← pow_succ]
      exact hlt
    · intro j hj
      rw [← digit_succ]
      exact hdig (j + 1) (by omega)
  · rintro ⟨h0, hlt, hdig⟩
    refine ⟨?_, ?_⟩
    · have hmod : X % P < P := Nat.mod_lt _ hP
      have hkey : P * (X / P) + X % P = X := Nat.div_add_mod X P
      calc X = P * (X / P) + X % P := hkey.symm
        _ < P * (X / P) + P := by omega
        _ = P * (X / P + 1) := by ring
        _ ≤ P * P ^ L := Nat.mul_le_mul_left _ hlt
        _ = P ^ (L + 1) := by rw [pow_succ, Nat.mul_comm]
    · intro j hj
      match j with
      | 0 => simpa [digit] using h0
      | (i + 1) => rw [digit_succ]; exact hdig i (by omega)

/-- The bottom level, counted: of the `P` residues below `P`, exactly the `|C|` in `C`
qualify. There is no free digit to multiply by — the contrast with the lift's `base_count`,
which returns `|S| · m^{k-1}`. -/
theorem word_base_count (P : ℕ) (hP : 0 < P) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    ((Finset.range P).filter (fun u => u % P ∈ C)).card = C.card := by
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hu, hmem⟩; rwa [Nat.mod_eq_of_lt hu] at hmem
  · intro hu; have := hC u hu; exact ⟨this, by rwa [Nat.mod_eq_of_lt this]⟩

/-- One level of the digit-string recursion, as a count: splitting `X` into `X % P` and
`X / P` is a bijection from `wordBlock P (L + 1) C` onto `C ×ˢ wordBlock P L C`. -/
private theorem wordBlock_succ_card (P L : ℕ) (hP : 0 < P) (C : Finset ℕ)
    (hC : ∀ c ∈ C, c < P) :
    (wordBlock P (L + 1) C).card = C.card * (wordBlock P L C).card := by
  have hcard : C.card * (wordBlock P L C).card = (C ×ˢ wordBlock P L C).card :=
    (Finset.card_product _ _).symm
  rw [hcard]
  refine Finset.card_nbij' (fun x => (x % P, x / P)) (fun p => p.1 + P * p.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, mem_wordBlock_succ P L C hP] at hx
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨hx.1, hx.2⟩
  · rintro ⟨u, v⟩ huv
    simp only [Finset.mem_coe, Finset.mem_product] at huv
    have hulp : u < P := hC u huv.1
    simp only [Finset.mem_coe, mem_wordBlock_succ P L C hP]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hulp, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hulp, Nat.zero_add]
    exact ⟨huv.1, huv.2⟩
  · intro x hx
    change x % P + P * (x / P) = x
    exact Nat.mod_add_div x P
  · rintro ⟨u, v⟩ huv
    simp only [Finset.mem_coe, Finset.mem_product] at huv
    have hulp : u < P := hC u huv.1
    change ((u + P * v) % P, (u + P * v) / P) = (u, v)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hulp, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hulp, Nat.zero_add]

/-- The digit-string bijection, where it is available. -/
theorem wordBlock_card_of_pos (P L : ℕ) (hP : 0 < P) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    (wordBlock P L C).card = C.card ^ L := by
  induction L with
  | zero => simp [wordBlock, digit]
  | succ L ih => rw [wordBlock_succ_card P L hP C hC, ih, pow_succ, Nat.mul_comm]

/-- The size count `|C^L| = |C|^L`, with no side condition on `P`: `P = 0` collapses `C`
to `∅` through `hC`, and both sides are then `0` for `L ≥ 1` and `1` for `L = 0`. -/
theorem wordBlock_card (P L : ℕ) (C : Finset ℕ) (hC : ∀ c ∈ C, c < P) :
    (wordBlock P L C).card = C.card ^ L := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · have he : C = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => by have := hC c hc; omega
    subst he
    match L with
    | 0 => simp [wordBlock, digit]
    | (n + 1) => simp [wordBlock]
  · exact wordBlock_card_of_pos P L hP C hC

/-! ## Lemma B -/

/-- The first half of the argument, entire: if two distinct words are congruent modulo
`P ^ L` up to a positive k-th power, the rank strictly drops from `X` to `Y`.

This is where the perfect-k-th-power hypothesis lives, and where the degenerate `n = 0` and
`n = 1` cases are discharged — the first empties the block, the second collapses `P ^ L` to
`1` so that `X = Y = 0` contradicts `hXY`. -/
theorem word_rank_drop_of_pow (k n P : ℕ) (hk : 1 ≤ k) (hP : P = n ^ k) (C : Finset ℕ)
    (h : ℕ → ℕ) (H : ℕ) (hC : RankedBlock k P C h H) (L : ℕ) (hL : 1 ≤ L) (X Y z : ℕ)
    (hX : X ∈ wordBlock P L C) (hY : Y ∈ wordBlock P L C) (hXY : X ≠ Y) (hz : 0 < z)
    (hcong : z ^ k % P ^ L = diffMod (P ^ L) X Y) :
    wordRank P L H h Y < wordRank P L H h X := by
  obtain ⟨-, hCbd, hCarc⟩ := hC
  obtain ⟨hXlt, hXC⟩ := (mem_wordBlock P L C X).mp hX
  obtain ⟨hYlt, hYC⟩ := (mem_wordBlock P L C Y).mp hY
  have hPLpos : 0 < P ^ L := Nat.lt_of_le_of_lt (Nat.zero_le X) hXlt
  have hP2 : 2 ≤ P := by
    rcases Nat.eq_zero_or_pos P with rfl | hPpos
    · rw [Nat.zero_pow (by omega)] at hPLpos; omega
    · rcases Nat.lt_or_ge P 2 with hlt | hge
      · have hP1 : P = 1 := by omega
        subst hP1
        rw [Nat.one_pow] at hXlt hYlt
        omega
      · exact hge
  have hHpos : 0 < H := Nat.lt_of_le_of_lt (Nat.zero_le _) (hCbd _ (hXC 0 (by omega)))
  have hdlt : diffMod (P ^ L) X Y < P ^ L := diffMod_lt _ X Y hPLpos
  have hd0 : diffMod (P ^ L) X Y ≠ 0 := diffMod_ne_zero _ X Y hXlt hYlt hXY
  obtain ⟨j, hjlt, hjne, hjlow⟩ := exists_least_digit_ne_of_lt k P L X Y hk hP2 hXlt hYlt hXY
  obtain ⟨hdvd1, hdvd2⟩ :=
    word_step0_exact_dvd k P L X Y j hk hP2 hL hXlt hYlt hjlt hjne hjlow
  have hks : P ^ j ∣ z ^ k :=
    word_step2_pow_dvd_pow k P L j z (diffMod (P ^ L) X Y) hjlt hcong hdvd1
  obtain ⟨u, hu⟩ := word_step3_root_split k n P j z hk hP hks
  have hlam : z ^ k = diffMod (P ^ L) X Y + z ^ k / P ^ L * P ^ L := by
    rw [← hcong]
    exact (Nat.mod_add_div' _ _).symm
  have hpow : IsNonzeroPowerMod k P (digit P j (diffMod (P ^ L) X Y)) :=
    word_step4_leading_power k P L j z (z ^ k / P ^ L) u (diffMod (P ^ L) X Y)
      hk hP2 hL hd0 hdlt hz.ne' hjlt hlam hu hdvd1 hdvd2
  rw [word_step1_leading_digit k P L X Y j hk hP2 hL hXlt hYlt hjlt hjlow] at hpow
  exact word_step5_rank_drop P L H j h C X Y hHpos hjlt hXC hYC hCbd hjlow
    (hCarc _ (hXC j hjlt) _ (hYC j hjlt) hjne hpow)

/-- The second half: a strict rank drop makes the code of `Y` *smaller* than the code of
`X`, because the whole word contributes at most `P^L - 1` while one unit of rank is worth
`P^L`. This is the contradiction that closes Lemma B. -/
theorem integerSet_lt_of_rank_lt (P L H : ℕ) (h : ℕ → ℕ) (X Y : ℕ) (hP : 0 < P)
    (hX : X < P ^ L) (hY : Y < P ^ L)
    (hlt : wordRank P L H h Y < wordRank P L H h X) :
    Y + P ^ L * wordRank P L H h Y + 1 < X + P ^ L * wordRank P L H h X + 1 := by
  have hmul : P ^ L * (wordRank P L H h Y + 1) ≤ P ^ L * wordRank P L H h X :=
    Nat.mul_le_mul_left _ hlt
  have hexp : P ^ L * (wordRank P L H h Y + 1)
      = P ^ L * wordRank P L H h Y + P ^ L := by ring
  omega

/-- **Lemma B.** For `P` a perfect k-th power and `C` a ranked block on `Z/PZ` of height
`H`, the integer set `A_L` has no two elements differing by a nonzero k-th power. -/
theorem lemmaB_pdf (k n P : ℕ) (hk : 1 ≤ k) (hP : P = n ^ k) (C : Finset ℕ) (h : ℕ → ℕ)
    (H : ℕ) (hC : RankedBlock k P C h H) (L : ℕ) (hL : 1 ≤ L) :
    PowerDifferenceFree k (integerSet P L H C h) := by
  intro a ha z hz hmem
  obtain ⟨X, hX, hXa⟩ := (mem_integerSet P L H C h a).mp ha
  obtain ⟨Y, hY, hYb⟩ := (mem_integerSet P L H C h (a + z ^ k)).mp hmem
  have hXlt : X < P ^ L := ((mem_wordBlock P L C X).mp hX).1
  have hYlt : Y < P ^ L := ((mem_wordBlock P L C Y).mp hY).1
  have hPLpos : 0 < P ^ L := Nat.lt_of_le_of_lt (Nat.zero_le X) hXlt
  have hP0 : 0 < P := by
    rcases Nat.eq_zero_or_pos P with rfl | hPpos
    · rw [Nat.zero_pow (by omega)] at hPLpos; omega
    · exact hPpos
  have hzk : 0 < z ^ k := pow_pos hz k
  have hXY : X ≠ Y := by
    rintro rfl
    omega
  have heq : X + z ^ k + P ^ L * wordRank P L H h X
      = Y + P ^ L * wordRank P L H h Y := by omega
  have hmod : (X + z ^ k) % P ^ L = Y := by
    rw [← Nat.add_mul_mod_self_left (X + z ^ k) (P ^ L) (wordRank P L H h X), heq,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hYlt]
  have hcong : z ^ k % P ^ L = diffMod (P ^ L) X Y :=
    (diffMod_unique (P ^ L) X Y (z ^ k) hPLpos hXlt hYlt hmod).symm
  have hdrop := word_rank_drop_of_pow k n P hk hP C h H hC L hL X Y z hX hY hXY hz hcong
  have hlt := integerSet_lt_of_rank_lt P L H h X Y hP0 hXlt hYlt hdrop
  omega

/-- `A_L ⊆ {1, …, (P H)^L}`: the interval bookkeeping. The translate by one supplies the
lower end; `X ≤ P^L - 1` and `h_L ≤ H^L - 1` supply the upper. -/
theorem integerSet_subset (k P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ)
    (hC : RankedBlock k P C h H) (hH : 1 ≤ H) :
    integerSet P L H C h ⊆ Finset.Icc 1 ((P * H) ^ L) := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := (mem_integerSet P L H C h a).mp ha
  obtain ⟨-, hCbd, -⟩ := hC
  obtain ⟨hXlt, hXC⟩ := (mem_wordBlock P L C X).mp hX
  have hw : wordRank P L H h X < H ^ L :=
    wordRank_lt_pow P L H h X (by omega) fun i hi => hCbd _ (hXC i hi)
  rw [Finset.mem_Icc, Nat.mul_pow]
  refine ⟨by omega, ?_⟩
  have hle : P ^ L * wordRank P L H h X + P ^ L ≤ P ^ L * H ^ L := by
    calc P ^ L * wordRank P L H h X + P ^ L = P ^ L * (wordRank P L H h X + 1) := by ring
      _ ≤ P ^ L * H ^ L := Nat.mul_le_mul_left _ hw
  omega

/-- `|A_L| = |C|^L`: `wordEmbed_injOn` plus `wordBlock_card`. -/
theorem integerSet_card (k P L H : ℕ) (C : Finset ℕ) (h : ℕ → ℕ)
    (hC : RankedBlock k P C h H) (hH : 1 ≤ H) :
    (integerSet P L H C h).card = C.card ^ L := by
  rw [integerSet, Finset.card_image_of_injOn (wordEmbed_injOn P L H C h)]
  exact wordBlock_card P L C hC.1

/-! ## The link to the counting function -/

/-- A k-th-power-difference-free subset of `{1, …, N}` is one of the sets `D k N` takes the
supremum over, so its size bounds `D k N` from below. -/
theorem le_D_of_pdf (k N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hpdf : PowerDifferenceFree k A) : A.card ≤ D k N := by
  unfold D
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hA, hpdf⟩

/-- The one inequality the exponent arithmetic consumes: a ranked block on a perfect
k-th-power modulus gives `D k` a lower bound at every word length. -/
theorem lemmaB_card_le_D (k n P : ℕ) (hk : 1 ≤ k) (hP : P = n ^ k) (C : Finset ℕ)
    (h : ℕ → ℕ) (H : ℕ) (hC : RankedBlock k P C h H) (hH : 1 ≤ H) (L : ℕ) (hL : 1 ≤ L) :
    C.card ^ L ≤ D k ((P * H) ^ L) := by
  rw [← integerSet_card k P L H C h hC hH]
  exact le_D_of_pdf k ((P * H) ^ L) (integerSet P L H C h)
    (integerSet_subset k P L H C h hC hH) (lemmaB_pdf k n P hk hP C h H hC L hL)

end KthPower
