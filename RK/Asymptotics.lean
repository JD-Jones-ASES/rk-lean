import RK.Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.unusedVariables false

/-!
# The limit formula and the passage to all `N`

The first half of this file allocates multiplicities `e_i(U) = ⌊U / log H_i⌋` to the
entries of a pool and shows that the exponent of the resulting stage tends to `alpha k P`
as `U → ∞`. The second half turns any single stage whose exponent exceeds `ρ` into a bound
`D k N ≥ N ^ ρ` valid for all large `N`, and then reads the liminf statement off the
family.

The two exports are `pointwise_internal` and `liminf_internal`, the two general targets of
`Challenge.lean` verbatim.

## The shape of the estimate, and why it is additive

The height estimate is `log H = U + O(1)`: the sandwich

`max_i H_i ^ e_i ≤ 1 + Σ_i (H_i ^ e_i - 1) ≤ ℓ · max_i H_i ^ e_i`,  `ℓ = P.length`,

together with `e_i(U) log H_i ∈ (U - log H_i, U]`. That is an *additive* `O(1)`, and the
numerator and denominator of the exponent are then `Θ(U)` with additive `O(1)` errors, so
the ratio converges. Nothing here is a ratio-of-limits abstraction; the two sandwich
lemmas `log_stageHeight_lower` and `log_stageHeight_upper` are the whole content.

The constants are supplied by the pool itself rather than by numerals: `bigLog P` is the
sum of the `log H_i`, which dominates each of them because every height is at least `2`,
and `P.length` is the number of blocks. A pool with an empty support is normalised away by
`fixPool` before the estimates run: replacing an empty support by the single vertex `0`
changes neither the exponent (`log 0 = log 1 = 0`) nor the validity of the pool, and it is
what lets the counting argument assume every block has a vertex to count.
-/

namespace KthPower

/-! ## The counting function is monotone, and bounded by its argument -/

/-- `D k` is monotone: a k-th-power-difference-free subset of `{1, …, N'}` is one of the
sets `D k N` takes the supremum over whenever `N' ≤ N`. -/
theorem D_mono (k : ℕ) : Monotone (D k) := by
  intro N N' h
  classical
  unfold D
  exact Finset.sup_mono
    (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr (Finset.Icc_subset_Icc_right h)))

/-- `D k N ≤ N`. Every competitor is a subset of `{1, …, N}`, which has `N` elements.
Trivial, and load-bearing: the liminf passage needs the sequence
`log (D k N) / log N` to be cobounded. -/
theorem D_le (k N : ℕ) : D k N ≤ N := by
  classical
  unfold D
  refine Finset.sup_le fun A hA => ?_
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  simpa [Nat.card_Icc] using Finset.card_le_card hsub

/-! ## The allocation -/

/-- `Σ_i log H_i` for a pool: a threshold that dominates every single `log H_i`, since all
of them are positive. It plays the role of `max_i log H_i` in the sandwich. -/
noncomputable def bigLog (P : List PoolEntry) : ℝ := (P.map fun b => Real.log b.2.2).sum

/-- The allocation `e_i(U) = ⌊U / log H_i⌋`, as a multiplicity vector in the sense of
`RK.Construction` — a function of the pool entry, which reads only its height. -/
noncomputable def alloc (U : ℝ) (b : PoolEntry) : ℕ := ⌊U / Real.log b.2.2⌋₊

/-- Every height in a pool has positive logarithm, because every height is at least `2`.
This is what makes `U / log H_i` a meaningful quantity at all. -/
theorem logHeight_pos (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ b ∈ P, 0 < Real.log b.2.2 := by
  intro b hb
  have h := (hP.2.2 b hb).2.2.1
  refine Real.log_pos ?_
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two h

/-- No single `log H_i` exceeds `bigLog P`: the sum of nonnegative terms dominates each
term. -/
theorem logHeight_le_bigLog (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ b ∈ P, Real.log b.2.2 ≤ bigLog P := by
  intro b hb
  have h0 : ∀ x ∈ P.map fun c => Real.log ((c.2.2 : ℕ) : ℝ), 0 ≤ x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact (logHeight_pos k P hP c hc).le
  exact List.single_le_sum h0 _ (List.mem_map_of_mem hb)

/-- `bigLog P` is positive for a nonempty pool. -/
theorem bigLog_pos (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) : 0 < bigLog P := by
  obtain ⟨b, hb⟩ : ∃ b, b ∈ P := by
    cases P with
    | nil => exact absurd rfl hP.1
    | cons c t => exact ⟨c, List.mem_cons_self⟩
  exact lt_of_lt_of_le (logHeight_pos k P hP b hb) (logHeight_le_bigLog k P hP b hb)

/-- Each multiplicity is at least `1` once `U` clears `bigLog P`, which is what makes the
lift applicable at every block. -/
theorem one_le_alloc (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (U : ℝ)
    (hU : bigLog P ≤ U) : ∀ b ∈ P, 1 ≤ alloc U b := by
  intro b hb
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (logHeight_pos k P hP b hb), one_mul]
  exact le_trans (logHeight_le_bigLog k P hP b hb) hU

/-- The upper half of `e_i(U) log H_i ∈ (U - log H_i, U]`. -/
theorem alloc_mul_logHeight_le (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (U : ℝ)
    (hU : 0 ≤ U) (b : PoolEntry) (hb : b ∈ P) :
    (alloc U b : ℝ) * Real.log b.2.2 ≤ U := by
  have hpos := logHeight_pos k P hP b hb
  have h : (alloc U b : ℝ) ≤ U / Real.log b.2.2 := Nat.floor_le (by positivity)
  rw [le_div_iff₀ hpos] at h
  exact h

/-- The lower half of `e_i(U) log H_i ∈ (U - log H_i, U]`. -/
theorem sub_logHeight_lt_alloc_mul (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (U : ℝ)
    (b : PoolEntry) (hb : b ∈ P) :
    U - Real.log b.2.2 < (alloc U b : ℝ) * Real.log b.2.2 := by
  have hpos := logHeight_pos k P hP b hb
  have h : U / Real.log b.2.2 < (alloc U b : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hpos] at h
  nlinarith

/-! ## The logarithms of the three closed forms -/

/-- `Real.log` of a list product of positive naturals is the sum of the logarithms. -/
private theorem log_natProd (l : List PoolEntry) (f : PoolEntry → ℕ) (hf : ∀ b ∈ l, 0 < f b) :
    Real.log (((l.map f).prod : ℕ) : ℝ) = (l.map fun b => Real.log ((f b : ℕ) : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : (0 : ℕ) < f a := hf a List.mem_cons_self
    have ht : ∀ b ∈ t, 0 < f b := fun b hb => hf b (List.mem_cons_of_mem _ hb)
    have hp : (0 : ℕ) < (t.map f).prod :=
      List.prod_pos (by
        intro n hn
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
        exact ht b hb)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hp.ne'), ih ht]

/-- Pulling a constant out of a mapped sum. -/
private theorem sum_map_const_mul (l : List PoolEntry) (c : ℝ) (g : PoolEntry → ℝ) :
    (l.map fun b => c * g b).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `log P = k Σ e_i log m_i`. -/
theorem log_stageModulus (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) :
    Real.log (stageModulus k P E)
      = (k : ℝ) * (P.map fun b => (E b : ℝ) * Real.log b.1).sum := by
  rw [stageModulus,
    log_natProd _ _ fun b hb => pow_pos (by have := (hP.2.2 b hb).1; omega) _]
  rw [List.map_congr_left (g := fun b => (k : ℝ) * ((E b : ℝ) * Real.log b.1))
    fun b _ => by push_cast; rw [Real.log_pow]; push_cast; ring]
  exact sum_map_const_mul _ (k : ℝ) _

/-- `log |C| = Σ e_i log (m_i^{k-1} t_i)`. -/
theorem log_stageCard (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) (E : PoolEntry → ℕ) :
    Real.log (stageCard k P E)
      = (P.map fun b => (E b : ℝ) * Real.log ((b.1 ^ (k - 1) * b.2.1.length : ℕ))).sum := by
  rw [stageCard, log_natProd _ _ fun b hb => pow_pos (Nat.mul_pos
    (pow_pos (by have := (hP.2.2 b hb).1; omega) _)
    (by have := baseBlocks_one_le_card k P hP hne b hb; omega)) _]
  exact congrArg List.sum (List.map_congr_left fun b _ => by push_cast; rw [Real.log_pow])

/-- `log (m^{k-1} t) = (k - 1) log m + log t`: the identity that turns the numerator of the
exponent formula into the weight the counting argument produces. -/
theorem log_natPow_mul (k m t : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    Real.log ((m ^ (k - 1) * t : ℕ)) = ((k : ℝ) - 1) * Real.log m + Real.log t := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hpow : ((m ^ (k - 1) : ℕ) : ℝ) = (m : ℝ) ^ (k - 1) := by push_cast; ring
  have hcast : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    have h := Nat.cast_sub (R := ℝ) hk
    simpa using h
  rw [Nat.cast_mul, hpow, Real.log_mul (by positivity) (ne_of_gt htR), Real.log_pow, hcast]

/-! ## The height sandwich -/

/-- The lower half: the height dominates each `H_i ^ e_i` on its own, because the sum
`1 + Σ (H_j ^ e_j - 1)` contains the term `H_i ^ e_i - 1` and every other term is
nonnegative. -/
theorem pow_height_le_stageHeight (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (b : PoolEntry) (hb : b ∈ P) :
    b.2.2 ^ E b ≤ stageHeight k P E := by
  have h1 : 1 ≤ b.2.2 ^ E b :=
    Nat.one_le_pow _ _ (by have := (hP.2.2 b hb).2.2.1; omega)
  have hmem : b.2.2 ^ E b - 1 ∈ P.map fun c => c.2.2 ^ E c - 1 := List.mem_map_of_mem hb
  have hsum := List.single_le_sum (l := P.map fun c => c.2.2 ^ E c - 1)
    (fun x _ => Nat.zero_le x) _ hmem
  rw [stageHeight]
  omega

/-- The upper half, with the maximum supplied by the caller: `ℓ` terms, each at most
`M - 1`, plus one, is at most `ℓ M` once `ℓ ≥ 1` and `M ≥ 1`. -/
theorem stageHeight_le_of_forall_le (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (M : ℕ) (hM : ∀ b ∈ P, b.2.2 ^ E b ≤ M) :
    stageHeight k P E ≤ P.length * M := by
  obtain ⟨b₀, hb₀⟩ : ∃ b, b ∈ P := by
    cases P with
    | nil => exact absurd rfl hP.1
    | cons c t => exact ⟨c, List.mem_cons_self⟩
  have hlen : (P.map fun c => c.2.2 ^ E c - 1).length = P.length := by simp
  have hterm : ∀ x ∈ P.map fun c => c.2.2 ^ E c - 1, x ≤ M - 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have := hM b hb
    omega
  have hsum := List.sum_le_card_nsmul _ (M - 1) hterm
  rw [hlen, smul_eq_mul] at hsum
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ b₀.2.2 ^ E b₀ :=
      Nat.one_le_pow _ _ (by have := (hP.2.2 b₀ hb₀).2.2.1; omega)
    have := hM b₀ hb₀
    omega
  have hlen1 : 1 ≤ P.length := by
    have : b₀ ∈ P := hb₀
    cases P with
    | nil => exact absurd rfl hP.1
    | cons c t => simp
  have hid : P.length * (M - 1) + P.length = P.length * M := by
    have hM' : M - 1 + 1 = M := by omega
    calc P.length * (M - 1) + P.length = P.length * (M - 1 + 1) := by ring
      _ = P.length * M := by rw [hM']
  rw [stageHeight]
  omega

/-- `log H ≥ U - bigLog P`, at the allocation. The witness is any single block:
`log (H_i ^ e_i(U)) = e_i(U) log H_i > U - log H_i ≥ U - bigLog P`. -/
theorem log_stageHeight_lower (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (U : ℝ)
    (hU : bigLog P ≤ U) : U - bigLog P ≤ Real.log (stageHeight k P (alloc U)) := by
  obtain ⟨b₀, hb₀⟩ : ∃ b, b ∈ P := by
    cases P with
    | nil => exact absurd rfl hP.1
    | cons c t => exact ⟨c, List.mem_cons_self⟩
  have hpos : (0 : ℕ) < b₀.2.2 ^ alloc U b₀ :=
    pow_pos (by have := (hP.2.2 b₀ hb₀).2.2.1; omega) _
  have hle := pow_height_le_stageHeight k P hP (alloc U) b₀ hb₀
  have hlog : Real.log ((b₀.2.2 ^ alloc U b₀ : ℕ) : ℝ)
      ≤ Real.log ((stageHeight k P (alloc U) : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  have heq : Real.log ((b₀.2.2 ^ alloc U b₀ : ℕ) : ℝ)
      = (alloc U b₀ : ℝ) * Real.log ((b₀.2.2 : ℕ) : ℝ) := by
    push_cast; rw [Real.log_pow]
  have h1 := sub_logHeight_lt_alloc_mul k P hP U b₀ hb₀
  have h2 := logHeight_le_bigLog k P hP b₀ hb₀
  rw [heq] at hlog
  linarith

/-- `log H ≤ U + log ℓ`, at the allocation, with `ℓ = P.length`. Every `H_i ^ e_i(U)` is at
most `exp U` because `e_i(U) log H_i ≤ U`, so the sandwich's upper half applies with
`M = ⌊exp U⌋`. The floor is the point: `⌈exp U⌉` rounds the wrong way once it is multiplied
by `ℓ`. -/
theorem log_stageHeight_upper (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (U : ℝ)
    (hU : bigLog P ≤ U) :
    Real.log (stageHeight k P (alloc U)) ≤ U + Real.log P.length := by
  have hbig : (0 : ℝ) < bigLog P := bigLog_pos k P hP
  have hU0 : (0 : ℝ) ≤ U := le_trans hbig.le hU
  have hexp1 : (1 : ℝ) ≤ Real.exp U := by
    have h := Real.exp_le_exp.mpr hU0
    rwa [Real.exp_zero] at h
  have hlen1 : 1 ≤ P.length := by
    cases P with
    | nil => exact absurd rfl hP.1
    | cons c t => simp
  set M := ⌊Real.exp U⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hexp1)
  have hkey : ∀ b ∈ P, b.2.2 ^ alloc U b ≤ M := by
    intro b hb
    refine Nat.le_floor ?_
    have hposr : (0 : ℝ) < ((b.2.2 ^ alloc U b : ℕ) : ℝ) := by
      have h : (0 : ℕ) < b.2.2 ^ alloc U b :=
        pow_pos (by have := (hP.2.2 b hb).2.2.1; omega) _
      exact_mod_cast h
    have hlog : Real.log ((b.2.2 ^ alloc U b : ℕ) : ℝ) ≤ U := by
      push_cast
      rw [Real.log_pow]
      exact alloc_mul_logHeight_le k P hP U hU0 b hb
    calc ((b.2.2 ^ alloc U b : ℕ) : ℝ)
        = Real.exp (Real.log ((b.2.2 ^ alloc U b : ℕ) : ℝ)) := (Real.exp_log hposr).symm
      _ ≤ Real.exp U := Real.exp_le_exp.mpr hlog
  have hH := stageHeight_le_of_forall_le k P hP (alloc U) M hkey
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hlenR : (0 : ℝ) < (P.length : ℝ) := by exact_mod_cast hlen1
  have hstep : Real.log ((stageHeight k P (alloc U) : ℕ) : ℝ)
      ≤ Real.log ((P.length * M : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast stageHeight_pos k P (alloc U)) (by exact_mod_cast hH)
  have hsplit : Real.log ((P.length * M : ℕ) : ℝ)
      = Real.log (P.length : ℝ) + Real.log (M : ℝ) := by
    push_cast
    exact Real.log_mul (ne_of_gt hlenR) (ne_of_gt hMR)
  have hMle : Real.log (M : ℝ) ≤ U := by
    have h1 : (M : ℝ) ≤ Real.exp U := Nat.floor_le (Real.exp_nonneg U)
    calc Real.log (M : ℝ) ≤ Real.log (Real.exp U) := Real.log_le_log hMR h1
      _ = U := Real.log_exp U
  rw [hsplit] at hstep
  linarith

/-! ## The exponent of a stage, and its limit -/

/-- The exponent a stage certifies: `log |C| / log (P H)`. Lemma B turns this into
`D k ((P H) ^ L) ≥ ((P H) ^ L) ^ α(e)`. -/
noncomputable def stageExponent (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : ℝ :=
  Real.log (stageCard k P E) / Real.log (stageModulus k P E * stageHeight k P E)

/-- The numerator of the exponent formula, in the form the counting argument produces it:
`Σ_i log (m_i^{k-1} t_i) / log H_i`. -/
noncomputable def alphaNum (k : ℕ) (P : List PoolEntry) : ℝ :=
  (P.map fun b => Real.log ((b.1 ^ (k - 1) * b.2.1.length : ℕ)) / Real.log b.2.2).sum

/-- The denominator of the exponent formula: `1 + k Σ_i log m_i / log H_i`. -/
noncomputable def alphaDen (k : ℕ) (P : List PoolEntry) : ℝ :=
  1 + (k : ℝ) * (P.map fun b => Real.log b.1 / Real.log b.2.2).sum

/-- The exponent of a pool as the ratio of those two sums. This is `log_natPow_mul`
applied under the numerator's `List.map`, and it is the seam between the pinned definition
of `alpha` and the shape the construction produces. -/
theorem alpha_eq_ratio (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) : alpha k P = alphaNum k P / alphaDen k P := by
  sorry

/-- The denominator is at least `1`: every term of `Σ log m_i / log H_i` is nonnegative. -/
theorem alphaDen_pos (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    0 < alphaDen k P := by
  have h : 0 ≤ (P.map fun b => Real.log b.1 / Real.log b.2.2).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (Real.log_natCast_nonneg _) (logHeight_pos k P hP b hb).le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [alphaDen]
  nlinarith

/-- The triangle inequality for two mapped sums: termwise `O(1)` control gives control of
the difference of the sums, with the constant the sum of the termwise ones. -/
private theorem abs_sum_map_sub_le (l : List PoolEntry) (f g w : PoolEntry → ℝ)
    (h : ∀ b ∈ l, |f b - g b| ≤ w b) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    calc |f a + (t.map f).sum - (g a + (t.map g).sum)|
        = |(f a - g a) + ((t.map f).sum - (t.map g).sum)| := by ring_nf
      _ ≤ |f a - g a| + |(t.map f).sum - (t.map g).sum| := abs_add_le _ _
      _ ≤ w a + (t.map w).sum := add_le_add h1 h2

/-- The shape of the per-block error: a nonnegative weight `L`, divided by a positive `h`,
times a quantity confined to `(-h, 0]`, is confined to `[-L, L]`. -/
private theorem abs_ratio_mul_le (L h x : ℝ) (hL : 0 ≤ L) (hh : 0 < h)
    (h1 : -h < x) (h2 : x ≤ 0) : |L / h * x| ≤ L := by
  have hLh : 0 ≤ L / h := div_nonneg hL hh.le
  have hid : L / h * h = L := div_mul_cancel₀ L (ne_of_gt hh)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left h1.le hLh
    rw [mul_neg, hid] at hm
    linarith
  · nlinarith

/-- **The `O(1)`, once for both sums.** For any nonnegative weight `w` on the pool,
`Σ_i e_i(U) w_i = U Σ_i w_i / log H_i + O(1)`, with the implied constant `Σ_i w_i`,
depending on the pool only. Both the numerator (`w = log (m_i^{k-1} t_i)`) and the modulus
part of the denominator (`w = log m_i`) are instances. -/
private theorem abs_alloc_weighted_sub_le (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (U : ℝ) (hU : 0 ≤ U) (w : PoolEntry → ℝ) (hw : ∀ b ∈ P, 0 ≤ w b) :
    |(P.map fun b => (alloc U b : ℝ) * w b).sum
        - U * (P.map fun b => w b / Real.log b.2.2).sum| ≤ (P.map w).sum := by
  rw [show U * (P.map fun b => w b / Real.log b.2.2).sum
      = (P.map fun b => U * (w b / Real.log b.2.2)).sum from
    (sum_map_const_mul _ _ _).symm]
  refine abs_sum_map_sub_le _ _ _ _ ?_
  intro b hb
  have hh : 0 < Real.log b.2.2 := logHeight_pos k P hP b hb
  have hlt : -Real.log b.2.2 < (alloc U b : ℝ) * Real.log b.2.2 - U := by
    have := sub_logHeight_lt_alloc_mul k P hP U b hb; linarith
  have hle : (alloc U b : ℝ) * Real.log b.2.2 - U ≤ 0 := by
    have := alloc_mul_logHeight_le k P hP U hU b hb; linarith
  have hid : (alloc U b : ℝ) * w b - U * (w b / Real.log b.2.2)
      = w b / Real.log b.2.2 * ((alloc U b : ℝ) * Real.log b.2.2 - U) := by
    field_simp
  rw [hid]
  exact abs_ratio_mul_le _ _ _ (hw b hb) hh hlt hle

/-- `g U = a U + O(1)` implies `g U / U → a`: squeeze between `a ± c/U`. -/
private theorem tendsto_div_atTop_of_abs_sub_le (a c : ℝ) (g : ℝ → ℝ)
    (hg : ∀ᶠ U in Filter.atTop, |g U - a * U| ≤ c) :
    Filter.Tendsto (fun U => g U / U) Filter.atTop (nhds a) := by
  have hc : Filter.Tendsto (fun U : ℝ => c / U) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id c
  have hlow : Filter.Tendsto (fun U : ℝ => a - c / U) Filter.atTop (nhds a) := by
    simpa using tendsto_const_nhds.sub hc
  have hhigh : Filter.Tendsto (fun U : ℝ => a + c / U) Filter.atTop (nhds a) := by
    simpa using tendsto_const_nhds.add hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [hg, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
    rw [le_div_iff₀ hU0, show (a - c / U) * U = a * U - c by field_simp]
    linarith [(abs_le.mp hU).1]
  · filter_upwards [hg, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
    rw [div_le_iff₀ hU0, show (a + c / U) * U = a * U + c by field_simp]
    linarith [(abs_le.mp hU).2]

/-- **The squeeze:** `(A U + O(1)) / (B U + O(1)) → A / B` when `B > 0`. Each of
`num U / U` and `den U / U` is squeezed on its own and the two limits divided. -/
private theorem tendsto_ratio_of_abs_sub_le (A B c₁ c₂ : ℝ) (hB : 0 < B) (num den : ℝ → ℝ)
    (hn : ∀ᶠ U in Filter.atTop, |num U - A * U| ≤ c₁)
    (hd : ∀ᶠ U in Filter.atTop, |den U - B * U| ≤ c₂) :
    Filter.Tendsto (fun U => num U / den U) Filter.atTop (nhds (A / B)) := by
  have h3 : Filter.Tendsto (fun U => num U / U / (den U / U)) Filter.atTop (nhds (A / B)) :=
    Filter.Tendsto.div (tendsto_div_atTop_of_abs_sub_le A c₁ num hn)
      (tendsto_div_atTop_of_abs_sub_le B c₂ den hd) (ne_of_gt hB)
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with U hU0
  exact div_div_div_cancel_right₀ (ne_of_gt hU0) _ _

/-- **The limit formula.** Along the allocation `e_i(U) = ⌊U / log H_i⌋`, the stage
exponent tends to the exponent of the pool.

The numerator is `U · Σ log (m_i^{k-1} t_i)/log H_i + O(1)` and the denominator is
`U · (1 + k Σ log m_i/log H_i) + O(1)`, both by the two halves of the allocation bound term
by term, so the ratio converges by the squeeze on `(A U + O(1)) / (B U + O(1))` with
`B > 0`. -/
theorem tendsto_stageExponent (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k)
    (hP : ValidPool k P) (hne : ∀ b ∈ P, b.2.1 ≠ []) :
    Filter.Tendsto (fun U : ℝ => stageExponent k P (alloc U)) Filter.atTop
      (nhds (alpha k P)) := by
  sorry

/-- The corollary the passage consumes: below the exponent of the pool there is an honest
finite stage, with every multiplicity positive and a stage size worth taking logarithms
of. -/
theorem exists_stage_exponent_gt (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k)
    (hP : ValidPool k P) (hne : ∀ b ∈ P, b.2.1 ≠ []) (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∃ E : PoolEntry → ℕ, (∀ b ∈ P, 1 ≤ E b) ∧
      1 < stageModulus k P E * stageHeight k P E ∧ ρ < stageExponent k P E := by
  have h1 : ∀ᶠ U : ℝ in Filter.atTop, ρ < stageExponent k P (alloc U) :=
    (tendsto_stageExponent k P hk hP hne).eventually_const_lt hρ
  obtain ⟨U, hU1, hU2⟩ := (h1.and (Filter.eventually_ge_atTop (bigLog P))).exists
  refine ⟨alloc U, one_le_alloc k P hP U hU2, ?_, hU1⟩
  have hPm := one_lt_stageModulus k P hk hP (alloc U) (one_le_alloc k P hP U hU2)
  have hH := (one_lt_stageHeight k P hP (alloc U) (one_le_alloc k P hP U hU2)).le
  calc 1 < stageModulus k P (alloc U) := hPm
    _ = stageModulus k P (alloc U) * 1 := (mul_one _).symm
    _ ≤ stageModulus k P (alloc U) * stageHeight k P (alloc U) := Nat.mul_le_mul_left _ hH

/-! ## From the special values to all `N`

The passage is a statement about two bare naturals `B ≥ 2` and `C ≥ 2` and nothing else:
if `C ^ L ≤ D k (B ^ L)` for every `L ≥ 1`, then `D k N ≥ N ^ ρ` eventually, for every `ρ`
below `log C / log B`. The stage enters only through `stage_D_bound`, at `B = P H` and
`C = |C|`. -/

/-- **The passage, with the stage abstracted away.** `B ^ L ≤ N < B ^ (L+1)` at
`L = ⌊log N / log B⌋` puts `N` between two consecutive special values, and monotonicity of
`D k` carries the count at the lower one up to `N`. The leftover factor `B ^ (-α)` is a
constant, absorbed because `N ^ (α - ρ) → ∞`; that absorption is where `ρ < α` is spent. -/
private theorem passage (k B C : ℕ) (hB : 2 ≤ B) (hC : 2 ≤ C) (ρ : ℝ)
    (hstage : ∀ L : ℕ, 1 ≤ L → C ^ L ≤ D k (B ^ L))
    (hρ : ρ < Real.log C / Real.log B) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  set α := Real.log C / Real.log B with hαdef
  have hb1 : (1 : ℝ) < B := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hB
  have hb0 : (0 : ℝ) < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hb1
  have hc1 : (1 : ℝ) < C := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hC
  have hlogC : 0 < Real.log C := Real.log_pos hc1
  have hα0 : 0 < α := div_pos hlogC hlogB
  have hBα : (B : ℝ) ^ α = (C : ℝ) := by
    rw [Real.rpow_def_of_pos hb0, hαdef,
      show Real.log B * (Real.log C / Real.log B) = Real.log C by field_simp]
    exact Real.exp_log (by linarith)
  have hBα0 : (0 : ℝ) < (B : ℝ) ^ α := Real.rpow_pos_of_pos hb0 α
  have habs : ∀ᶠ N : ℕ in Filter.atTop, (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (N : ℝ) ^ α := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (α - ρ)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by linarith)
    have h1' : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (α - ρ)) Filter.atTop Filter.atTop :=
      h1.comp tendsto_natCast_atTop_atTop
    filter_upwards [h1'.eventually_ge_atTop ((B : ℝ) ^ α), Filter.eventually_ge_atTop 1]
      with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hp : (0 : ℝ) < (N : ℝ) ^ ρ := Real.rpow_pos_of_pos hN0 ρ
    have h2 := mul_le_mul_of_nonneg_right hN hp.le
    rwa [← Real.rpow_add hN0, sub_add_cancel] at h2
  filter_upwards [habs, Filter.eventually_ge_atTop B, Filter.eventually_ge_atTop 1]
    with N hN hNB hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNB' : (B : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNB
  have hN1' : (1 : ℝ) < N := lt_of_lt_of_le hb1 hNB'
  have hlogN : 0 < Real.log N := Real.log_pos hN1'
  set L := ⌊Real.log N / Real.log B⌋₊ with hL
  have hnn : (0 : ℝ) ≤ Real.log N / Real.log B :=
    div_nonneg (Real.log_natCast_nonneg _) hlogB.le
  have hLratio : (1 : ℝ) ≤ Real.log N / Real.log B :=
    (one_le_div hlogB).mpr (Real.log_le_log hb0 hNB')
  have hL1 : 1 ≤ L := Nat.le_floor (by exact_mod_cast hLratio)
  have hfl : (L : ℝ) ≤ Real.log N / Real.log B := Nat.floor_le hnn
  have hBLle : (B : ℝ) ^ L ≤ (N : ℝ) := by
    have h : (L : ℝ) * Real.log B ≤ Real.log N := by rw [← le_div_iff₀ hlogB]; exact hfl
    have h2 : Real.log ((B : ℝ) ^ L) ≤ Real.log N := by rw [Real.log_pow]; exact h
    exact (Real.log_le_log_iff (by positivity) hN0).mp h2
  have hBLleN : B ^ L ≤ N := by exact_mod_cast hBLle
  have hNlt : (N : ℝ) < (B : ℝ) ^ (L + 1) := by
    have h := Nat.lt_floor_add_one (Real.log N / Real.log B)
    rw [← hL] at h
    have h2 : Real.log N < ((L : ℝ) + 1) * Real.log B := by rw [← div_lt_iff₀ hlogB]; exact h
    have h3 : Real.log N < Real.log ((B : ℝ) ^ (L + 1)) := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_lt_log_iff hN0 (by positivity)).mp h3
  have hcount : (C : ℝ) ^ L ≤ (D k N : ℝ) := by
    have h1 := hstage L hL1
    have h2 : D k (B ^ L) ≤ D k N := D_mono k hBLleN
    have h3 : C ^ L ≤ D k N := le_trans h1 h2
    exact_mod_cast h3
  have hCL : (B : ℝ) ^ (α * (L : ℝ)) = (C : ℝ) ^ L := by
    rw [Real.rpow_mul hb0.le, hBα, Real.rpow_natCast]
  have hupper : (N : ℝ) ^ α ≤ (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := by
    have h1 : (N : ℝ) ^ α ≤ ((B : ℝ) ^ (L + 1)) ^ α :=
      Real.rpow_le_rpow hN0.le hNlt.le hα0.le
    have h2 : ((B : ℝ) ^ (L + 1)) ^ α = (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := by
      rw [← Real.rpow_natCast (B : ℝ) (L + 1), ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
      push_cast; ring_nf
    rwa [h2] at h1
  have hkey : (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (B : ℝ) ^ α * (D k N : ℝ) := by
    calc (B : ℝ) ^ α * (N : ℝ) ^ ρ ≤ (N : ℝ) ^ α := hN
      _ ≤ (B : ℝ) ^ (α * (L : ℝ)) * (B : ℝ) ^ α := hupper
      _ = (C : ℝ) ^ L * (B : ℝ) ^ α := by rw [hCL]
      _ ≤ (D k N : ℝ) * (B : ℝ) ^ α := by nlinarith
      _ = (B : ℝ) ^ α * (D k N : ℝ) := by ring
  exact le_of_mul_le_mul_left hkey hBα0

/-- **The passage at a fixed stage.** With `P H > 1` and `α(e) > ρ`, the stage bound and
the monotonicity of `D k` give `D k N ≥ N ^ ρ` for all large `N`. -/
theorem stage_pointwise (k : ℕ) (P : List PoolEntry) (hk : 2 ≤ k) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b)
    (hPH : 1 < stageModulus k P E * stageHeight k P E) (ρ : ℝ)
    (hρ : ρ < stageExponent k P E) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  refine passage k (stageModulus k P E * stageHeight k P E) (stageCard k P E) (by omega)
    (by have := one_lt_stageCard k P hk hP hne E hE; omega) ρ
    (fun L hL => stage_D_bound k P (by omega) hP E hE L hL) ?_
  rw [Nat.cast_mul]
  exact hρ

/-- The pointwise bound for a pool with no empty support. -/
theorem pointwise_of_ne_nil (k : ℕ) (P : List PoolEntry) (hk : 2 ≤ k) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  obtain ⟨E, hE, hPH, hex⟩ := exists_stage_exponent_gt k P (by omega) hP hne ρ hρ
  exact stage_pointwise k P hk hP hne E hE hPH ρ hex

/-! ## Normalising a pool with an empty support

`ValidPool` does not forbid an empty support list: the emptiness conditions of a ranked
support are vacuous. Such a block contributes `log 0 = 0` to the numerator of the exponent,
exactly as a one-vertex block contributes `log 1 = 0`, so replacing it by the block with
the single vertex `0` at rank `0` changes neither the exponent nor the validity of the pool
— and it is what lets the counting argument assume every block has a vertex. -/

/-- A pool entry with an empty support replaced by the single vertex `0` at rank `0`. -/
def fixEntry (b : PoolEntry) : PoolEntry :=
  if b.2.1 = [] then (b.1, [(0, 0)], b.2.2) else b

/-- A pool with every empty support replaced by a one-vertex support. -/
def fixPool (P : List PoolEntry) : List PoolEntry := P.map fixEntry

/-- The normalised pool has no empty support. -/
theorem fixPool_sup_ne_nil (P : List PoolEntry) : ∀ b ∈ fixPool P, b.2.1 ≠ [] := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  unfold fixEntry
  by_cases h : c.2.1 = []
  · simp [h]
  · simp [h]

/-- The normalised pool is a pool: the moduli and heights are untouched, and the single
vertex `0` at rank `0` is a ranked support modulo any `m ≥ 2` of any height `H ≥ 2`. -/
theorem fixPool_valid (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ValidPool k (fixPool P) := by
  sorry

/-- Normalising a pool does not change its exponent: the only quantity that moves is
`log t` at a block with `t = 0`, and `Real.log 0 = 0 = Real.log 1`. -/
theorem alpha_fixPool (k : ℕ) (P : List PoolEntry) : alpha k (fixPool P) = alpha k P := by
  sorry

/-! ## The two general targets -/

/-- **The directed construction at every `k`, pointwise form.** For `k ≥ 2`, every pool `P`
for `k` and every `ρ < alpha k P`, `N ^ ρ ≤ D_k(N)` for all sufficiently large `N`. -/
theorem pointwise_internal (k : ℕ) (hk : 2 ≤ k) (P : List PoolEntry) (hP : ValidPool k P)
    (ρ : ℝ) (hρ : ρ < alpha k P) :
    ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ ρ ≤ (D k N : ℝ) := by
  refine pointwise_of_ne_nil k (fixPool P) hk (fixPool_valid k P hP)
    (fixPool_sup_ne_nil P) ρ ?_
  rw [alpha_fixPool k P]
  exact hρ

/-- **The directed construction at every `k`, liminf form.** For `k ≥ 2` and every pool `P`
for `k`, `alpha k P ≤ liminf log D_k(N) / log N`.

The cobounded side condition of `Filter.le_liminf_of_le` is paid with `D_le`: `D k N ≤ N`
gives `log (D k N) / log N ≤ 1` for `N ≥ 2`. -/
theorem liminf_internal (k : ℕ) (hk : 2 ≤ k) (P : List PoolEntry) (hP : ValidPool k P) :
    alpha k P ≤
      Filter.liminf (fun N : ℕ => Real.log (D k N) / Real.log N) Filter.atTop := by
  set u : ℕ → ℝ := fun N => Real.log (D k N) / Real.log N with hu
  have hb : ∀ᶠ N : ℕ in Filter.atTop, u N ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have hlogN : 0 < Real.log N := Real.log_pos hN1
    have hDN : (D k N : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le k N
    have hlog : Real.log (D k N) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos (D k N) with h0 | h0
      · rw [h0]; simpa using hlogN.le
      · exact Real.log_le_log (by exact_mod_cast h0) hDN
    rw [hu]; simp only
    rw [div_le_one hlogN]
    exact hlog
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨1, hb⟩
  refine le_of_forall_lt_imp_le_of_dense fun ρ hρ => ?_
  refine Filter.le_liminf_of_le hcob ?_
  filter_upwards [pointwise_internal k hk P hP ρ hρ, Filter.eventually_ge_atTop 2] with N h hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ ρ := Real.rpow_pos_of_pos hN0 ρ
  have hlog : Real.log ((N : ℝ) ^ ρ) ≤ Real.log (D k N) := Real.log_le_log hpos h
  rw [Real.log_rpow hN0] at hlog
  rw [hu]; simp only
  rw [le_div_iff₀ hlogN]
  linarith

end KthPower
