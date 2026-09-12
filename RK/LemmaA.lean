import RK.RankedBlocks
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option linter.unusedVariables false

/-!
# Lemma A — the composite digit lift at every `k`

A ranked block `S` on `Z/mZ`, for square-free `m ≥ 2`, lifts to a ranked block on
`Z/m^{ke}Z`: the residues whose base-`m` digits at the positions `k j`, `j < e`, all lie
in `S`, ranked by the base-`H₀` number `Σ_{j<e} h₀(x_{kj}) H₀^{e-1-j}`. The lifted block
has `(m^{k-1} |S|)^e` elements — `e` constrained digits and `e (k-1)` free ones — and
height `H₀ ^ e`.

The headline is `lemmaA`. Everything above it is the step spine, one named lemma per step
of the argument:

| Lean | step |
| --- | --- |
| `exists_least_digit_ne` | the least differing base-`m` position `r` |
| `step0_exact_dvd` | `m ^ r ∣ d`, `m ^ (r+1) ∤ d`, i.e. `r = v_m(d)` |
| `step1_leading_digit` | `δ := (d / m^r) mod m ≡ y_r - x_r`, no borrows below `r` |
| `pow_dvd_iff_forall_prime`, `exists_padicValNat_eq` | `v_m(d) = min_q v_q(d)` |
| `padicValNat_add_of_lt` | the dominated-term move, as a toolkit lemma |
| `step2_uncapped`, `step2_capped` | the two coordinate kinds |
| `step2_dvd` | `k ∣ r` (and `r < k e`) |
| `step3_pow_dvd` | the global divisibility `m ^ j ∣ z` |
| `step4_leading_power` | the leading digit is a nonzero k-th-power residue mod `m` |
| `liftRank_split`, `liftRank_tail_lt`, `step5_rank_drop` | the geometric assembly |

The one place the exponent `k` does real work is Step 2. In an uncapped coordinate
`v_q(d) = v_q(z ^ k) = k v_q(z)`, so the valuation of a nonzero k-th-power residue is a
multiple of `k`; a capped coordinate has `v_q(d) ≥ k e` and cannot attain the minimum,
which is `< k e`. Square-freeness of `m` is what makes `v_m(d)` that minimum, and it enters
at exactly two points: `exists_padicValNat_eq` (some prime attains `v_m(d)` exactly) and
`pow_dvd_iff_forall_prime` (the per-prime bounds reassemble into `m ^ j ∣ z`).

The step lemmas carry the standing hypotheses of the argument whether or not their proofs
consume them, so that a reader checking Lean against the prose never has to reconcile two
different lists of assumptions.
-/

namespace KthPower

/-! ## Digits -/

/-- The `j`-th base-`m` digit of `x`. Digits are a `ℕ`-valued *function*, never a list:
`liftBlock` and `liftRank` are conditions on digits, not enumerations of digit strings. -/
def digit (m j x : ℕ) : ℕ := x / m ^ j % m

/-- Digits are residues. -/
theorem digit_lt (m j x : ℕ) (hm : 0 < m) : digit m j x < m :=
  Nat.mod_lt _ hm

/-- Digits above the leading position vanish. -/
theorem digit_eq_zero_of_lt (m j x : ℕ) (hx : x < m ^ j) : digit m j x = 0 := by
  simp [digit, Nat.div_eq_of_lt hx]

/-- Peeling one digit off the bottom: the `(j+1)`-st digit of `x` is the `j`-th digit of
`x / m`. This is the induction hook for `eq_of_digits_eq`, and the word stage peels the
same digit at radix `P`. -/
theorem digit_succ (m j x : ℕ) : digit m (j + 1) x = digit m j (x / m) := by
  unfold digit
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm,
    ← Nat.div_div_eq_div_mul]

/-- Adding a multiple of `m ^ (j + 1)` leaves the `j`-th digit alone: the carry lands
strictly above position `j`. This is the "no borrows" mechanism of Step 1. -/
theorem digit_add_mul_pow_succ (m j x c : ℕ) (hm : 0 < m) :
    digit m j (x + c * m ^ (j + 1)) = digit m j x := by
  have hp : 0 < m ^ j := Nat.pow_pos hm
  have hrw : x + c * m ^ (j + 1) = x + m ^ j * (c * m) := by ring
  unfold digit
  rw [hrw, Nat.add_mul_div_left _ _ hp, Nat.add_mul_mod_self_right]

/-- If `m ^ r ∣ d` then every digit of `d` below position `r` is zero. -/
theorem digit_eq_zero_of_pow_dvd (m r i d : ℕ) (hm : 0 < m) (hi : i < r) (hdvd : m ^ r ∣ d) :
    digit m i d = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = i + 1 + s := ⟨r - i - 1, by omega⟩
  obtain ⟨c, rfl⟩ := hdvd
  have hp : 0 < m ^ i := Nat.pow_pos hm
  have hrw : m ^ (i + 1 + s) * c = m ^ i * (m * (m ^ s * c)) := by
    rw [pow_add, pow_add, pow_one]; ring
  rw [digit, hrw, Nat.mul_div_cancel_left _ hp, Nat.mul_mod_right]

/-- Two residues below `m ^ n` agreeing in all `n` digits are equal. The contrapositive is
what produces the least differing position of Step 0. -/
private theorem eq_of_digits_eq_aux (m : ℕ) (hm : 0 < m) :
    ∀ (n x y : ℕ), x < m ^ n → y < m ^ n → (∀ j < n, digit m j x = digit m j y) → x = y := by
  intro n
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy h
    have h0 : x % m = y % m := by simpa [digit] using h 0 (Nat.succ_pos n)
    have hd : x / m = y / m := by
      refine ih _ _ ?_ ?_ ?_
      · rw [Nat.div_lt_iff_lt_mul hm]; rw [pow_succ] at hx; omega
      · rw [Nat.div_lt_iff_lt_mul hm]; rw [pow_succ] at hy; omega
      · intro j hj; rw [← digit_succ, ← digit_succ]; exact h (j + 1) (by omega)
    calc x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      _ = m * (y / m) + y % m := by rw [hd, h0]
      _ = y := Nat.div_add_mod y m

theorem eq_of_digits_eq (m n x y : ℕ) (hm : 2 ≤ m) (hx : x < m ^ n) (hy : y < m ^ n)
    (hdig : ∀ i < n, digit m i x = digit m i y) :
    x = y :=
  eq_of_digits_eq_aux m (by omega) n x y hx hy hdig

/-- Truncating `x` at `m ^ n` leaves every digit below position `n` untouched. -/
private theorem digit_mod_pow (m n i x : ℕ) (hi : i < n) :
    digit m i (x % m ^ n) = digit m i x := by
  have hK : m ^ n = m ^ i * m ^ (n - i) := by rw [← pow_add]; congr 1; omega
  have hd : m ∣ m ^ (n - i) := dvd_pow_self m (by omega)
  unfold digit
  rw [hK, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd]

/-- Agreement of the bottom `n` digits *is* congruence modulo `m ^ n`. This is the digit
workhorse the low-position bookkeeping runs on. -/
theorem mod_pow_eq_iff_digits_eq (m n x y : ℕ) (hm : 2 ≤ m) :
    x % m ^ n = y % m ^ n ↔ ∀ i < n, digit m i x = digit m i y := by
  have hm0 : 0 < m := by omega
  have hpow : 0 < m ^ n := Nat.pow_pos hm0
  constructor
  · intro h i hi
    rw [← digit_mod_pow m n i x hi, ← digit_mod_pow m n i y hi, h]
  · intro h
    refine eq_of_digits_eq m n _ _ hm (Nat.mod_lt _ hpow) (Nat.mod_lt _ hpow) ?_
    intro i hi
    rw [digit_mod_pow m n i x hi, digit_mod_pow m n i y hi]
    exact h i hi

/-- Step 0's `r`: the least base-`m` position at which two distinct residues below
`m ^ (k * e)` differ. It exists and is `< k * e`. -/
theorem exists_least_digit_ne (k m e x y : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e)) (hxy : x ≠ y) :
    ∃ r, r < k * e ∧ digit m r x ≠ digit m r y ∧ ∀ i < r, digit m i x = digit m i y := by
  have hex : ∃ i, i < k * e ∧ digit m i x ≠ digit m i y := by
    by_contra hcon
    refine hxy (eq_of_digits_eq m (k * e) x y hm hx hy fun i hi => ?_)
    by_contra hne
    exact hcon ⟨i, hi, hne⟩
  obtain ⟨i₀, hi₀lt, hi₀ne⟩ := hex
  have hP : ∃ j, digit m j x ≠ digit m j y := ⟨i₀, hi₀ne⟩
  refine ⟨Nat.find hP, lt_of_le_of_lt (Nat.find_min' hP hi₀ne) hi₀lt, Nat.find_spec hP, ?_⟩
  intro i hi
  exact not_not.mp (Nat.find_min hP hi)

/-! ## The lift -/

/-- The lifted block: the residues below `m ^ (k * e)` whose base-`m` digits at the
positions `0, k, 2k, …, (e-1)k` all lie in `S`. The other `e (k-1)` digits are
unconstrained, and they are what supplies the factor `m ^ (k-1)` in the size count. -/
def liftBlock (k m e : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (m ^ (k * e))).filter (fun x => ∀ j < e, digit m (k * j) x ∈ S)

/-- The lifted ranking: `h(x) = Σ_{j<e} h₀(x_{kj}) · H₀^{e-1-j}`, the base-`H₀` number
whose digits are the ranks of the constrained digits, most significant first. -/
def liftRank (k m e H₀ : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range e, h₀ (digit m (k * j) x) * H₀ ^ (e - 1 - j)

/-- Membership in the lifted block, unfolded. -/
theorem mem_liftBlock (k m e : ℕ) (S : Finset ℕ) (x : ℕ) :
    x ∈ liftBlock k m e S ↔ x < m ^ (k * e) ∧ ∀ j < e, digit m (k * j) x ∈ S := by
  simp [liftBlock, Finset.mem_filter, Finset.mem_range]

/-- A base-`H` string of length `n`, least significant digit first, is `< H ^ n`. -/
private theorem sum_coeff_lt_pow (H : ℕ) (c : ℕ → ℕ) :
    ∀ n, (∀ i < n, c i < H) → ∑ i ∈ Finset.range n, c i * H ^ i < H ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le _) (h n (by omega))
    have hlt := ih fun i hi => h i (by omega)
    calc ∑ i ∈ Finset.range (n + 1), c i * H ^ i
        = (∑ i ∈ Finset.range n, c i * H ^ i) + c n * H ^ n := Finset.sum_range_succ _ _
      _ < H ^ n + c n * H ^ n := by omega
      _ = (c n + 1) * H ^ n := by ring
      _ ≤ H * H ^ n := Nat.mul_le_mul_right _ (h n (by omega))
      _ = H ^ (n + 1) := by ring

/-- The same bound with the weights reversed — most significant digit first, which is the
order the lifted and word ranks use. -/
theorem sum_reflect_lt_pow (H : ℕ) (a : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, a i < H) :
    ∑ i ∈ Finset.range n, a i * H ^ (n - 1 - i) < H ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | -
  · simp
  have key : ∑ i ∈ Finset.range n, a i * H ^ (n - 1 - i)
      = ∑ i ∈ Finset.range n, a (n - 1 - i) * H ^ i := by
    rw [← Finset.sum_range_reflect (fun i => a (n - 1 - i) * H ^ i) n]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hji : n - 1 - (n - 1 - j) = j := by omega
    rw [hji]
  rw [key]
  exact sum_coeff_lt_pow H (fun i => a (n - 1 - i)) n fun i hi => h _ (by omega)

/-- The lifted rank is a base-`H₀` string of length `e`, hence `< H₀ ^ e`: the height
claim of Lemma A's conclusion. -/
theorem liftRank_lt_pow (k m e H₀ : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hH : 0 < H₀)
    (hb : ∀ i < e, h₀ (digit m (k * i) x) < H₀) :
    liftRank k m e H₀ h₀ x < H₀ ^ e :=
  sum_reflect_lt_pow H₀ (fun i => h₀ (digit m (k * i) x)) e hb

/-- `liftRank` split at position `j`: the digits below `j`, the digit at `j`, the tail. -/
theorem liftRank_split (k m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hj : j < e) :
    liftRank k m e H₀ h₀ x =
      (∑ i ∈ Finset.range j, h₀ (digit m (k * i) x) * H₀ ^ (e - 1 - i))
        + h₀ (digit m (k * j) x) * H₀ ^ (e - 1 - j)
        + ∑ i ∈ Finset.Ico (j + 1) e, h₀ (digit m (k * i) x) * H₀ ^ (e - 1 - i) := by
  rw [liftRank, ← Finset.sum_range_add_sum_Ico
    (fun i => h₀ (digit m (k * i) x) * H₀ ^ (e - 1 - i)) (Nat.succ_le_of_lt hj),
    Finset.sum_range_succ]

/-- The geometric bound of Step 5: everything above position `j` is worth strictly less
than one unit at position `j`, since `(H₀ - 1) Σ_{j' > j} H₀^{e-1-j'} = H₀^{e-1-j} - 1`. -/
theorem liftRank_tail_lt (k m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (x : ℕ) (hH : 0 < H₀) (hj : j < e)
    (hb : ∀ i < e, h₀ (digit m (k * i) x) < H₀) :
    ∑ i ∈ Finset.Ico (j + 1) e, h₀ (digit m (k * i) x) * H₀ ^ (e - 1 - i)
      < H₀ ^ (e - 1 - j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hN : e - 1 - j = e - (j + 1) := by omega
  have hcongr : ∑ i ∈ Finset.range (e - (j + 1)),
        h₀ (digit m (k * (j + 1 + i)) x) * H₀ ^ (e - 1 - (j + 1 + i))
      = ∑ i ∈ Finset.range (e - (j + 1)),
        h₀ (digit m (k * (j + 1 + i)) x) * H₀ ^ (e - (j + 1) - 1 - i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  rw [hN, hcongr]
  exact sum_reflect_lt_pow H₀ (fun i => h₀ (digit m (k * (j + 1 + i)) x)) (e - (j + 1))
    fun i hi => hb _ (by omega)

/-! ## Step 0 — exact divisibility -/

/-- Reducing `x + d` modulo any `m ^ j` with `j ≤ k * e` recovers `y`: the wraparound term
`κ m ^ (k * e)` is a multiple of `m ^ j`, so it is invisible below position `k * e`. -/
private theorem diffMod_add_mod_pow (k m e x y j : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e)) (hj : j ≤ k * e) :
    (x + diffMod (m ^ (k * e)) x y) % m ^ j = y % m ^ j := by
  have hm0 : 0 < m := by omega
  have hMpos : 0 < m ^ (k * e) := Nat.pow_pos hm0
  obtain ⟨c, hc⟩ : m ^ j ∣ m ^ (k * e) := Nat.pow_dvd_pow m hj
  rcases diffMod_add (m ^ (k * e)) x y hMpos hx hy with h | h
  · rw [h]
  · rw [h, hc, Nat.add_mul_mod_self_left]

/-- The divisibility half of Step 0, isolated: agreement of the digits below `r` already
forces `m ^ r ∣ d`. Step 1 needs this too, without Step 0's `hne`. -/
private theorem pow_dvd_diffMod (k m e x y r : ℕ) (hm : 2 ≤ m)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e)) (hr : r ≤ k * e)
    (hlow : ∀ i < r, digit m i x = digit m i y) :
    m ^ r ∣ diffMod (m ^ (k * e)) x y := by
  have hxy : x % m ^ r = y % m ^ r := (mod_pow_eq_iff_digits_eq m r x y hm).mpr hlow
  have h1 : x ≡ x + diffMod (m ^ (k * e)) x y [MOD m ^ r] := by
    unfold Nat.ModEq
    rw [diffMod_add_mod_pow k m e x y r hm hx hy hr, hxy]
  simpa using (Nat.modEq_iff_dvd' (Nat.le_add_right x _)).mp h1

/-- **Step 0.** With `r` the least differing digit position, `r = v_m(d)` for
`d = diffMod (m ^ (k * e)) x y`: exactly `r` factors of `m` divide `d`. The wraparound
`κ m^{ke}` does not disturb this because `r < k * e`. -/
theorem step0_exact_dvd (k m e x y r : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (he : 1 ≤ e)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e)) (hr : r < k * e)
    (hne : digit m r x ≠ digit m r y) (hlow : ∀ i < r, digit m i x = digit m i y) :
    m ^ r ∣ diffMod (m ^ (k * e)) x y ∧ ¬ m ^ (r + 1) ∣ diffMod (m ^ (k * e)) x y := by
  refine ⟨pow_dvd_diffMod k m e x y r hm hx hy (by omega) hlow, ?_⟩
  rintro ⟨c, hc⟩
  have h1 : (x + diffMod (m ^ (k * e)) x y) % m ^ (r + 1) = y % m ^ (r + 1) :=
    diffMod_add_mod_pow k m e x y (r + 1) hm hx hy (by omega)
  rw [hc, Nat.add_mul_mod_self_left] at h1
  exact hne ((mod_pow_eq_iff_digits_eq m (r + 1) x y hm).mp h1 r (by omega))

/-! ## Step 1 — the leading digit, without borrows -/

/-- **Step 1.** The `r`-th digit of the difference is the difference of the `r`-th digits:
positions above `r` contribute multiples of `m`, positions below `r` agree, and the
wraparound contributes `m^{ke-r} ≡ 0`. -/
theorem step1_leading_digit (k m e x y r : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (he : 1 ≤ e)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e)) (hr : r < k * e)
    (hlow : ∀ i < r, digit m i x = digit m i y) :
    digit m r (diffMod (m ^ (k * e)) x y) = diffMod m (digit m r x) (digit m r y) := by
  have hm0 : 0 < m := by omega
  have hpr : 0 < m ^ r := Nat.pow_pos hm0
  have hMpos : 0 < m ^ (k * e) := Nat.pow_pos hm0
  obtain ⟨D, hD⟩ := pow_dvd_diffMod k m e x y r hm hx hy (by omega) hlow
  have hDdiv : diffMod (m ^ (k * e)) x y / m ^ r = D := by
    rw [hD, Nat.mul_div_cancel_left _ hpr]
  -- the borrow-free relation at position `r`, before reducing mod `m`
  have hkey : (x / m ^ r + D) % m = (y / m ^ r) % m := by
    rcases diffMod_add (m ^ (k * e)) x y hMpos hx hy with h | h
    · rw [hD] at h
      rw [← h, Nat.add_mul_div_left _ _ hpr]
    · rw [hD] at h
      have hsplit : m ^ (k * e) = m ^ r * (m * m ^ (k * e - r - 1)) := by
        rw [← pow_succ']
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at h
      have h2 : (x + m ^ r * D) / m ^ r
          = (y + m ^ r * (m * m ^ (k * e - r - 1))) / m ^ r := by rw [h]
      rw [Nat.add_mul_div_left _ _ hpr, Nat.add_mul_div_left _ _ hpr] at h2
      rw [h2, Nat.add_mul_mod_self_left]
  have huniq : diffMod m (digit m r x) (digit m r y)
      = digit m r (diffMod (m ^ (k * e)) x y) % m := by
    refine diffMod_unique m (digit m r x) (digit m r y)
      (digit m r (diffMod (m ^ (k * e)) x y)) hm0 (digit_lt m r x hm0) (digit_lt m r y hm0) ?_
    unfold digit
    rw [hDdiv, ← Nat.add_mod, hkey]
  rw [huniq, Nat.mod_eq_of_lt (digit_lt m r _ hm0)]

/-! ## Step 2 — the valuation of a nonzero k-th-power residue is a multiple of `k` -/

/-- For square-free `m`, a common power of `m` divides `d` exactly when the same power of
each prime factor of `m` does. The proof runs on `Nat.factorization`, where
square-freeness is `v_q(m) ≤ 1`. -/
private theorem sf_pow_dvd_iff {m : ℕ} (hsf : Squarefree m) (hm : m ≠ 0) {j d : ℕ}
    (hd : d ≠ 0) : m ^ j ∣ d ↔ ∀ q ∈ m.primeFactors, q ^ j ∣ d := by
  constructor
  · intro h q hq
    exact dvd_trans (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hq) j) h
  · intro h
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hm) hd, Nat.factorization_pow,
      Finsupp.le_def]
    intro q
    by_cases hq : q ∈ m.primeFactors
    · have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have h1 : m.factorization q ≤ 1 := (Nat.squarefree_iff_factorization_le_one hm).mp hsf q
      have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hqp hd).mp (h q hq)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      calc j * m.factorization q ≤ j * 1 := Nat.mul_le_mul_left _ h1
        _ = j := by ring
        _ ≤ d.factorization q := h2
    · have hz : m.factorization q = 0 := by
        simpa [Nat.support_factorization] using (Finsupp.notMem_support_iff).mp
          (by simpa [Nat.support_factorization] using hq)
      simp [hz]

/-- Exact divisibility survives the addition of a strictly more divisible term. This is the
`ℕ`-level stand-in for `emultiplicity_add_of_gt`, which is gated on `[Ring α]`. -/
private theorem exact_dvd_add {p j a b : ℕ} (ha : p ^ j ∣ a) (hna : ¬ p ^ (j + 1) ∣ a)
    (hb : p ^ (j + 1) ∣ b) : p ^ j ∣ a + b ∧ ¬ p ^ (j + 1) ∣ a + b :=
  ⟨dvd_add ha ((pow_dvd_pow p (Nat.le_succ j)).trans hb),
    fun h => hna ((Nat.dvd_add_right hb).mp (by rwa [Nat.add_comm a b] at h))⟩

/-- The same move run backwards: exact divisibility of `a + b` descends to `a` when `b` is
strictly more divisible. This is the direction Steps 2 and 3 need, since it is `z ^ k`
whose valuation is known and `d` whose valuation is wanted. -/
private theorem exact_dvd_of_add {p j a b : ℕ} (hb : p ^ (j + 1) ∣ b)
    (h1 : p ^ j ∣ a + b) (h2 : ¬ p ^ (j + 1) ∣ a + b) :
    p ^ j ∣ a ∧ ¬ p ^ (j + 1) ∣ a := by
  have hbk : p ^ j ∣ b := (pow_dvd_pow p (Nat.le_succ j)).trans hb
  exact ⟨(Nat.dvd_add_right hbk).mp (by rwa [Nat.add_comm a b] at h1),
    fun h => h2 (dvd_add h hb)⟩

/-- Exact divisibility names the valuation. -/
private theorem padicValNat_eq_of_exact {q j n : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (h1 : q ^ j ∣ n) (h2 : ¬ q ^ (j + 1) ∣ n) : padicValNat q n = j := by
  have : Fact q.Prime := ⟨hq⟩
  have hle : j ≤ padicValNat q n := (padicValNat_dvd_iff_le hn).mp h1
  have hlt : ¬ (j + 1 ≤ padicValNat q n) := fun h => h2 ((padicValNat_dvd_iff_le hn).mpr h)
  omega

/-- Square-freeness as a valuation statement: `v_q(m) = 1` for every prime `q ∣ m`, so
`m ^ r ∣ d` iff `q ^ r ∣ d` for each of them. This is `v_m(d) = min_q v_q(d)` in the form
Step 2 uses it. -/
theorem pow_dvd_iff_forall_prime (m d r : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hd : d ≠ 0) :
    m ^ r ∣ d ↔ ∀ q : ℕ, q.Prime → q ∣ m → r ≤ padicValNat q d := by
  have hm0 : m ≠ 0 := by omega
  rw [sf_pow_dvd_iff hsf hm0 hd]
  constructor
  · intro h q hq hqm
    have : Fact q.Prime := ⟨hq⟩
    exact (padicValNat_dvd_iff_le hd).mp (h q (Nat.mem_primeFactors.mpr ⟨hq, hqm, hm0⟩))
  · intro h q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    exact (padicValNat_dvd_iff_le hd).mpr (h q hqp (Nat.dvd_of_mem_primeFactors hq))

/-- Exact divisibility exhibits a prime attaining the minimum: `r = v_m(d)` means some
`q ∣ m` has `v_q(d) = r` exactly. -/
theorem exists_padicValNat_eq (m d r : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hd : d ≠ 0)
    (h1 : m ^ r ∣ d) (h2 : ¬ m ^ (r + 1) ∣ d) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ padicValNat q d = r := by
  have hlow := (pow_dvd_iff_forall_prime m d r hm hsf hd).mp h1
  by_contra hcon
  refine h2 ((pow_dvd_iff_forall_prime m d (r + 1) hm hsf hd).mpr fun q hq hqm => ?_)
  have hge := hlow q hq hqm
  rcases Nat.lt_or_ge (padicValNat q d) (r + 1) with hlt | hge'
  · exact absurd ⟨q, hq, hqm, by omega⟩ hcon
  · exact hge'

/-- The dominated-term move: a strictly smaller valuation wins in a sum. Step 2's uncapped
case is this applied to `z ^ k = d + lam * m ^ (k * e)`. -/
theorem padicValNat_add_of_lt (q a b : ℕ) (hq : q.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : padicValNat q a < padicValNat q b) :
    padicValNat q (a + b) = padicValNat q a := by
  have : Fact q.Prime := ⟨hq⟩
  have h1 : q ^ padicValNat q a ∣ a := pow_padicValNat_dvd
  have h2 : ¬ q ^ (padicValNat q a + 1) ∣ a := pow_succ_padicValNat_not_dvd ha
  have h3 : q ^ (padicValNat q a + 1) ∣ b := (padicValNat_dvd_iff_le hb).mpr (by omega)
  obtain ⟨h4, h5⟩ := exact_dvd_add h1 h2 h3
  exact padicValNat_eq_of_exact hq (by omega) h4 h5

/-- **Step 2, uncapped coordinate.** When `k v_q(z) < k e`, the k-th-power term dominates
and `v_q(d) = k v_q(z)` — a multiple of `k`. -/
theorem step2_uncapped (k m e d z lam q : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m)
    (hq : q.Prime) (hqm : q ∣ m) (hd : d ≠ 0) (hz : z ≠ 0)
    (hlam : z ^ k = d + lam * m ^ (k * e)) (hunc : padicValNat q z < e) :
    padicValNat q d = k * padicValNat q z := by
  sorry

/-- **Step 2, capped coordinate.** When `v_q(z) ≥ e`, both terms are divisible by
`q ^ (k e)`, so `v_q(d) ≥ k e` and the coordinate carries no information about `k ∣ r` —
and cannot attain the minimum, which is `< k e`. -/
theorem step2_capped (k m e d z lam q : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m)
    (hq : q.Prime) (hqm : q ∣ m) (hd : d ≠ 0) (hz : z ≠ 0)
    (hlam : z ^ k = d + lam * m ^ (k * e)) (hcap : e ≤ padicValNat q z) :
    k * e ≤ padicValNat q d := by
  sorry

/-- **Step 2 (headline).** `r = v_m(d)` is a minimum of multiples of `k`, hence a multiple
of `k`. This is where square-freeness is essential: for `m = 9` and `k = 2`, `d = 9` has
`v_m(d) = 1`. -/
theorem step2_dvd (k m e d z lam r : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m)
    (he : 1 ≤ e) (hd : d ≠ 0) (hdlt : d < m ^ (k * e)) (hz : z ≠ 0)
    (hlam : z ^ k = d + lam * m ^ (k * e))
    (hr : r < k * e) (h1 : m ^ r ∣ d) (h2 : ¬ m ^ (r + 1) ∣ d) :
    k ∣ r := by
  sorry

/-! ## Step 3 — global divisibility -/

/-- **Step 3.** With `r = k * j`, every coordinate satisfies `v_q(z) ≥ j`: uncapped ones
because `k v_q(z) ≥ r`, capped ones because `v_q(z) ≥ e > j`. Square-freeness then
assembles the coordinates into `m ^ j ∣ z`. -/
theorem step3_pow_dvd (k m e j d z lam : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m)
    (he : 1 ≤ e) (hd : d ≠ 0) (hdlt : d < m ^ (k * e)) (hz : z ≠ 0)
    (hlam : z ^ k = d + lam * m ^ (k * e)) (hj : j < e)
    (h1 : m ^ (k * j) ∣ d) (h2 : ¬ m ^ (k * j + 1) ∣ d) :
    m ^ j ∣ z := by
  sorry

/-! ## Step 4 — the leading digit is a nonzero k-th-power residue mod `m` -/

/-- **Step 4.** Writing `z = m ^ j * u`, we get `d / m^{kj} ≡ u ^ k (mod m^{ke-kj})` with
`k e - k j ≥ k ≥ 1`, so reducing modulo `m` puts the leading digit `δ` in the image of
`z ↦ z ^ k` with witness `u % m`, and `δ ≠ 0` because `m ^ (k j + 1)` does not divide `d`.
Note that `u` need not be a unit: `δ` can be a non-unit k-th-power residue, which is
exactly why `IsNonzeroPowerMod` is the full image with `0` removed. -/
theorem step4_leading_power (k m e j d z lam u : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m)
    (hsf : Squarefree m) (he : 1 ≤ e) (hd : d ≠ 0) (hdlt : d < m ^ (k * e)) (hz : z ≠ 0)
    (hlam : z ^ k = d + lam * m ^ (k * e)) (hj : j < e)
    (h1 : m ^ (k * j) ∣ d) (h2 : ¬ m ^ (k * j + 1) ∣ d) (hu : z = m ^ j * u) :
    IsNonzeroPowerMod k m (digit m (k * j) d) := by
  sorry

/-! ## Step 5 — the rank drop -/

/-- **Step 5.** A drop of at least one unit at the constrained position `k j`, equal digits
below it, and the geometric tail bound above it, give a strict drop in the lifted rank. -/
theorem step5_rank_drop (k m e H₀ j : ℕ) (h₀ : ℕ → ℕ) (S : Finset ℕ) (x y : ℕ)
    (hH : 0 < H₀) (hj : j < e)
    (hxS : ∀ i < e, digit m (k * i) x ∈ S) (hyS : ∀ i < e, digit m (k * i) y ∈ S)
    (hbd : ∀ s ∈ S, h₀ s < H₀)
    (hlow : ∀ i < j, digit m (k * i) x = digit m (k * i) y)
    (hdrop : h₀ (digit m (k * j) y) < h₀ (digit m (k * j) x)) :
    liftRank k m e H₀ h₀ y < liftRank k m e H₀ h₀ x := by
  have hby : ∀ i < e, h₀ (digit m (k * i) y) < H₀ := fun i hi => hbd _ (hyS i hi)
  have htail := liftRank_tail_lt k m e H₀ j h₀ y hH hj hby
  have hmul : (h₀ (digit m (k * j) y) + 1) * H₀ ^ (e - 1 - j)
      ≤ h₀ (digit m (k * j) x) * H₀ ^ (e - 1 - j) := Nat.mul_le_mul_right _ hdrop
  have hexp : (h₀ (digit m (k * j) y) + 1) * H₀ ^ (e - 1 - j)
      = h₀ (digit m (k * j) y) * H₀ ^ (e - 1 - j) + H₀ ^ (e - 1 - j) := by ring
  have hlowsum : (∑ i ∈ Finset.range j, h₀ (digit m (k * i) x) * H₀ ^ (e - 1 - i))
      = ∑ i ∈ Finset.range j, h₀ (digit m (k * i) y) * H₀ ^ (e - 1 - i) :=
    Finset.sum_congr rfl fun i hi => by rw [hlow i (Finset.mem_range.mp hi)]
  rw [liftRank_split k m e H₀ j h₀ x hj, liftRank_split k m e H₀ j h₀ y hj, hlowsum]
  omega

/-! ## Lemma A -/

/-- **Lemma A (the composite digit lift).** A ranked block on `Z/mZ` for square-free
`m ≥ 2` lifts to a ranked block on `Z/m^{ke}Z` of height `H₀ ^ e`. -/
theorem lemmaA (k m : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m)
    (S : Finset ℕ) (h₀ : ℕ → ℕ) (H₀ : ℕ)
    (hS : RankedBlock k m S h₀ H₀) (e : ℕ) (he : 1 ≤ e) :
    RankedBlock k (m ^ (k * e)) (liftBlock k m e S) (liftRank k m e H₀ h₀) (H₀ ^ e) := by
  sorry

/-! ## The size count -/

/-- Peeling `k` digit positions off the bottom: position `i + k` of `x` is position `i` of
`x / m ^ k`. This is the digit half of the `x ↦ (x % m^k, x / m^k)` split that drives the
count, one lifted block level per `m ^ k`. -/
private theorem digit_add_pow (k m i x : ℕ) : digit m (i + k) x = digit m i (x / m ^ k) := by
  have h : x / m ^ (i + k) = x / m ^ k / m ^ i := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm k i]
  unfold digit
  rw [h]

/-- One level of the block, split at `m ^ k`: the bottom `k` digits contribute the single
constraint `x mod m ∈ S` together with `k - 1` free digits, and everything above is a block
of one level less on `x / m ^ k`. This is the recursion `liftBlock_card` runs on. -/
private theorem mem_liftBlock_succ (k m e : ℕ) (S : Finset ℕ) (hk : 1 ≤ k) (hm : 0 < m)
    (x : ℕ) :
    x ∈ liftBlock k m (e + 1) S ↔ x % m ∈ S ∧ x / m ^ k ∈ liftBlock k m e S := by
  sorry

/-- The bottom level, counted: of the `m ^ k` residues below `m ^ k`, exactly
`|S| · m^{k-1}` have their last digit in `S` — `k - 1` free digits times the constrained
one. -/
private theorem base_count (k m : ℕ) (hk : 1 ≤ k) (hm : 0 < m) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s < m) :
    ((Finset.range (m ^ k)).filter (fun u => u % m ∈ S)).card = S.card * m ^ (k - 1) := by
  sorry

/-- The size count for `m ≥ 2`, where the digit-string bijection runs: a residue below
`m ^ (k * (e + 1))` splits as a bottom group of `k` digits — one constrained to `S`, the
other `k - 1` free — times a residue below `m ^ (k * e)`. -/
private theorem liftBlock_card_of_two_le (k m e : ℕ) (S : Finset ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m)
    (hS : ∀ s ∈ S, s < m) :
    (liftBlock k m e S).card = (m ^ (k - 1) * S.card) ^ e := by
  sorry

/-- The size count `|C(k, m, S, e)| = (m^{k-1} t)^e`: `e (k-1)` free digits and `e` digits
from `S`. The degenerate moduli `m ≤ 1` are settled by inspection, `hS` having collapsed
`S` to `∅` or `{0}`. -/
theorem liftBlock_card (k m e : ℕ) (S : Finset ℕ) (hk : 1 ≤ k) (hS : ∀ s ∈ S, s < m) :
    (liftBlock k m e S).card = (m ^ (k - 1) * S.card) ^ e := by
  sorry

end KthPower
