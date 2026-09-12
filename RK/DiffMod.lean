import RK.Defs

set_option linter.unusedVariables false

/-!
# The `diffMod` toolkit

`diffMod m a b = (b + m - a) % m` is the residue of `b - a` modulo `m`, computed in `ℕ` so
that every finite claim about a concrete modulus stays decidable. This file collects the
facts about that definition which the rest of the development uses at every modulus: it
lands in `[0, m)`, it is nonzero on distinct residues, it moves `a` to `b` up to one
wraparound, and it is *the* shift from `a` to `b` for any witness of the congruence.

The last declaration is the other fact every stage needs about a nonzero k-th-power
residue: the λ-decomposition `z ^ k = d + lam * M`, produced once from
`IsNonzeroPowerMod`, which is what turns the arc condition of a ranked block into an
equation the digit and valuation arguments can work on.
-/

namespace KthPower

/-- `diffMod` lands in `[0, M)`. -/
theorem diffMod_lt (M a b : ℕ) (hM : 0 < M) : diffMod M a b < M :=
  Nat.mod_lt _ hM

/-- Distinct residues have a nonzero difference. -/
theorem diffMod_ne_zero (M x y : ℕ) (hx : x < M) (hy : y < M) (hxy : x ≠ y) :
    diffMod M x y ≠ 0 := by
  unfold diffMod
  by_cases h : x ≤ y
  · have h1 : y + M - x = y - x + M := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The `κ ∈ {0, 1}` wraparound in `ℕ`: `x + d` is either `y` or `y + M`. Stating it once
keeps `ℤ` out of every statement downstream. -/
theorem diffMod_add (M x y : ℕ) (hM : 0 < M) (hx : x < M) (hy : y < M) :
    x + diffMod M x y = y ∨ x + diffMod M x y = y + M := by
  unfold diffMod
  by_cases h : x ≤ y
  · left
    have h1 : y + M - x = y - x + M := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `diffMod m a b` is *the* shift from `a` to `b`, for any witness `c` — not only for a
witness already reduced: `a + c ≡ b (mod m)` forces `diffMod m a b = c % m`. The digit
argument identifies the leading digit of a difference by exhibiting it as such a `c`; the
word argument's witness is a k-th power `z ^ k`, which is not reduced. -/
theorem diffMod_unique (m a b c : ℕ) (hm : 0 < m) (ha : a < m) (hb : b < m)
    (h : (a + c) % m = b) : diffMod m a b = c % m := by
  have hc : c % m < m := Nat.mod_lt _ hm
  have h' : (a + c % m) % m = b := by rw [← h]; simp [Nat.add_mod]
  clear h
  unfold diffMod
  by_cases hlt : a + c % m < m
  · rw [Nat.mod_eq_of_lt hlt] at h'
    subst h'
    have hrw : a + c % m + m - a = c % m + m := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
  · have h2 : (a + c % m) % m = a + c % m - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h'
    subst h'
    have hrw : a + c % m - m + m - a = c % m := by omega
    rw [hrw, Nat.mod_eq_of_lt hc]

/-- The λ-decomposition, produced once from the `IsNonzeroPowerMod` hypothesis a ranked
block carries: a nonzero k-th-power residue `d < M` is `z ^ k - lam * M` for some `z ≠ 0`
below `M`. The exponent `k` is positive, which is what rules out the witness `z = 0`. -/
theorem exists_lambda_of_isNonzeroPowerMod (k M d : ℕ) (hk : 1 ≤ k) (hM : 0 < M) (hd : d < M)
    (hpow : IsNonzeroPowerMod k M d) :
    d ≠ 0 ∧ ∃ z lam : ℕ, z ≠ 0 ∧ z < M ∧ z ^ k = d + lam * M := by
  obtain ⟨hne, z, hzM, hz⟩ := hpow
  rw [Nat.mod_eq_of_lt hd] at hne hz
  refine ⟨hne, z, z ^ k / M, ?_, hzM, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega : k ≠ 0), Nat.zero_mod] at hz
    exact hne hz.symm
  · calc z ^ k = M * (z ^ k / M) + z ^ k % M := (Nat.div_add_mod _ _).symm
      _ = M * (z ^ k / M) + d := by rw [hz]
      _ = d + z ^ k / M * M := by ring

end KthPower
