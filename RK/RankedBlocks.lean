import RK.DiffMod

set_option linter.unusedVariables false

/-!
# Ranked blocks — the predicate the whole chain speaks

`ValidRankedSupport` (in `RK.Defs`) is the *list* form of a ranked block: it is what the
concrete pools satisfy, and it is decidable, which is why `decide` can check them in the
kernel. It is a poor interface for the lift, which has to quantify over a set of residues
modulo `m ^ (k * e)` far too large to enumerate.

`RankedBlock k P C h H` below is the *functional* form of the same idea: a `Finset` of
vertices, a ranking given as a plain function `ℕ → ℕ`, and the same two conditions —
ranks below `H`, and a strict rank drop along every arc, where an arc is an ordered pair
whose difference is a nonzero k-th-power residue modulo `P` (`IsNonzeroPowerMod`, the full
image of `z ↦ z ^ k` with `0` removed; the unit-only variant would make the lift false).

With `P = m` this is "k-th-power DAG on `Z/mZ` with a ranking of height `H`". Acyclicity
is not stated separately: it follows from the existence of the ranking. The lift takes
`RankedBlock` to `RankedBlock`, and the gluing and counting stages consume the same
predicate, so this is the one interface that crosses every stage boundary.

`supportFinset` is `(sup.map Prod.fst).toFinset` and `rankOf` is `List.lookup` with `0` as
the junk value off the support. A total function with junk values keeps the lifted ranking
a plain `ℕ → ℕ`; the junk value is never observed, because every use is guarded by
membership in the support.
-/

namespace KthPower

/-- A ranked block on `Z/PZ` for the exponent `k`: the vertices `C` are residues `< P`,
the ranks are `< H`, and along every arc — every ordered pair whose difference is a
nonzero k-th-power residue modulo `P` — the rank strictly drops.

With `P = m` this is a ranked support with its list structure forgotten; with
`P = m ^ (k * e)` it is the conclusion of the lift. One predicate, both ends. -/
def RankedBlock (k P : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ) : Prop :=
  (∀ x ∈ C, x < P) ∧ (∀ x ∈ C, h x < H) ∧
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → IsNonzeroPowerMod k P (diffMod P x y) → h y < h x

/-- The vertex set of a ranked support, as a `Finset`. -/
def supportFinset (sup : List (ℕ × ℕ)) : Finset ℕ := (sup.map Prod.fst).toFinset

/-- The ranking of a ranked support, as a total function: the rank recorded for `x` if `x`
is on the support, and the junk value `0` otherwise. Off-support values are never
observed — every use is guarded by membership in the support. -/
def rankOf (sup : List (ℕ × ℕ)) (x : ℕ) : ℕ := (sup.lookup x).getD 0

/-- Membership in `supportFinset` is "some rank is recorded for `x`". -/
theorem mem_supportFinset (sup : List (ℕ × ℕ)) (x : ℕ) :
    x ∈ supportFinset sup ↔ ∃ r : ℕ, (x, r) ∈ sup := by
  simp only [supportFinset, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨a, r⟩, hp, rfl⟩
    exact ⟨r, hp⟩
  · rintro ⟨r, hr⟩
    exact ⟨(x, r), hr, rfl⟩

/-- On a support with pairwise distinct vertices, `rankOf` reads back the recorded rank. -/
theorem rankOf_eq_of_mem (sup : List (ℕ × ℕ)) (x r : ℕ)
    (hd : sup.Pairwise (fun p q => p.1 ≠ q.1)) (hx : (x, r) ∈ sup) :
    rankOf sup x = r := by
  unfold rankOf
  induction sup with
  | nil => simp at hx
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.mp hx with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq x r a b ▸ h
      simp [List.lookup]
    · have hne : ¬ (x = a) := fun hxa => hd.1 (x, r) h (by simp [hxa])
      have hbeq : (x == a) = false := beq_eq_false_iff_ne.mpr hne
      simp only [List.lookup, hbeq]
      exact ih hd.2 h

/-- Pairwise distinct vertices means no collapse: the support size is the list length.
This is what identifies the `t` of the exponent formula with the number of vertices. -/
theorem supportFinset_card (sup : List (ℕ × ℕ))
    (hd : sup.Pairwise (fun p q => p.1 ≠ q.1)) :
    (supportFinset sup).card = sup.length := by
  have hnd : (sup.map Prod.fst).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hd
  rw [supportFinset, List.toFinset_card_of_nodup hnd, List.length_map]

/-- The bridge from the decidable data to the functional predicate: a ranked support is a
ranked block, so a `decide`-checked pool can be fed to the lift. -/
theorem RankedBlock.of_validRankedSupport (k m H : ℕ) (sup : List (ℕ × ℕ))
    (hv : ValidRankedSupport k m sup H) :
    RankedBlock k m (supportFinset sup) (rankOf sup) H := by
  obtain ⟨hd, hbd, harc⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := (mem_supportFinset sup x).mp hx
    exact (hbd (x, r) hr).1
  · intro x hx
    obtain ⟨r, hr⟩ := (mem_supportFinset sup x).mp hx
    rw [rankOf_eq_of_mem sup x r hd hr]
    exact (hbd (x, r) hr).2
  · intro x hx y hy hxy hpow
    obtain ⟨rx, hrx⟩ := (mem_supportFinset sup x).mp hx
    obtain ⟨ry, hry⟩ := (mem_supportFinset sup y).mp hy
    rw [rankOf_eq_of_mem sup x rx hd hrx, rankOf_eq_of_mem sup y ry hd hry]
    exact harc (x, rx) hrx (y, ry) hry hxy hpow

/-- The support of a ranked support consists of residues — the hypothesis the size count
of the lift takes. -/
theorem supportFinset_lt_of_valid (k m H : ℕ) (sup : List (ℕ × ℕ))
    (hv : ValidRankedSupport k m sup H) : ∀ s ∈ supportFinset sup, s < m := by
  intro s hs
  obtain ⟨r, hr⟩ := (mem_supportFinset sup s).mp hs
  exact (hv.2.1 (s, r) hr).1

end KthPower
