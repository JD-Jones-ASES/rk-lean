import RK.LemmaA
import RK.LemmaB
import RK.LemmaC

set_option linter.unusedVariables false

/-!
# The glued stage construction

The blocks of a pool, lifted with multiplicities and glued by the Chinese remainder
theorem into a single ranked block on a perfect k-th-power modulus, which Lemma B then
turns into a lower bound on the counting function. Writing `(m_i, sup_i, H_i)` for the
entries of the pool, `t_i` for the number of vertices of `sup_i`, and `e_i` for the
multiplicity allotted to the `i`-th entry, the outcome is

`P = Π m_i ^ (k e_i)`,  `|C| = Π (m_i^{k-1} t_i) ^ e_i`,  `H = 1 + Σ (H_i ^ e_i - 1)`,

and those three are `stageModulus`, `stageCard` and `stageHeight` below. The one
inequality this file exports is `stage_D_bound`:

`stageCard ^ L ≤ D k ((stageModulus * stageHeight) ^ L)` for every `L ≥ 1`,

which is the display above fed to Lemma B. Everything between connects the pool to the
three closed forms.

## The multiplicity vector

The allocation used by the asymptotic argument, `e_i(U) = ⌊U / log H_i⌋`, depends on the
entry only through its height. The multiplicity therefore travels as a *function of the
pool entry*, `E : PoolEntry → ℕ`, rather than as a vector: the entries of a pool are
distinct, so a function on entries restricts to an arbitrary vector, and the asymptotic
layer instantiates it at the allocation without any indexing apparatus. Every closed form
below is a `List.map` over the pool, which is what makes the logarithms a `List.sum`
exchange rather than an induction.
-/

namespace KthPower

set_option maxRecDepth 10000

/-! ## Blocks and pool entries -/

/-- A pool entry as it appears in `ValidPool`: `(modulus, ranked support, height)`. -/
abbrev PoolEntry : Type := ℕ × List (ℕ × ℕ) × ℕ

/-- The block a pool entry stands for: the same modulus and height, with the support list
read as a `Finset` and its ranking as a total function. -/
def baseBlockOf (b : PoolEntry) : Block := (b.1, supportFinset b.2.1, rankOf b.2.1, b.2.2)

/-- The blocks of a pool. -/
def baseBlocks (P : List PoolEntry) : List Block := P.map baseBlockOf

/-- One block lifted to multiplicity `e`, in the shape `lemmaA` produces: modulus
`m ^ (k e)`, support `liftBlock`, ranking `liftRank`, height `H ^ e`. -/
def liftOf (k : ℕ) (b : Block) (e : ℕ) : Block :=
  (b.1 ^ (k * e), liftBlock k b.1 e b.2.1, liftRank k b.1 e b.2.2.2 b.2.2.1, b.2.2.2 ^ e)

/-- The lifted blocks of a pool at multiplicity vector `E`. -/
def stageBlocks (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : List Block :=
  P.map (fun b => liftOf k (baseBlockOf b) (E b))

/-! ## The three closed forms -/

/-- `Π m_i ^ e_i` — the k-th root of the stage modulus, which is what Lemma B's
perfect-k-th-power hypothesis needs exhibited. -/
def stageRoot (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : ℕ :=
  (P.map fun b => b.1 ^ E b).prod

/-- `P = Π m_i ^ (k e_i)`. -/
def stageModulus (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : ℕ :=
  (P.map fun b => b.1 ^ (k * E b)).prod

/-- `|C| = Π (m_i^{k-1} t_i) ^ e_i`. -/
def stageCard (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : ℕ :=
  (P.map fun b => (b.1 ^ (k - 1) * b.2.1.length) ^ E b).prod

/-- `H = 1 + Σ (H_i ^ e_i - 1)`. -/
def stageHeight (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) : ℕ :=
  1 + (P.map fun b => b.2.2 ^ E b - 1).sum

/-! ## What the blocks of a pool are

The hypotheses `lemmaA`, `lemmaC` and `lemmaB_card_le_D` take, read off `ValidPool` once so
that no proof below re-derives them. -/

/-- A nonempty list has a member. -/
private theorem exists_mem_of_ne_nil (P : List PoolEntry) (h : P ≠ []) : ∃ b, b ∈ P := by
  cases P with
  | nil => exact absurd rfl h
  | cons b t => exact ⟨b, List.mem_cons_self⟩

/-- The blocks carry the moduli of the pool. -/
theorem baseBlocks_moduli (P : List PoolEntry) :
    (baseBlocks P).map Prod.fst = P.map Prod.fst := by
  simp [baseBlocks, baseBlockOf, List.map_map, Function.comp_def]

/-- There are as many blocks as pool entries. -/
theorem baseBlocks_length (P : List PoolEntry) : (baseBlocks P).length = P.length := by
  simp [baseBlocks]

/-- A pool is nonempty, hence so is its list of blocks. -/
theorem baseBlocks_ne_nil (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    baseBlocks P ≠ [] := by
  simp only [baseBlocks, ne_eq, List.map_eq_nil_iff]
  exact hP.1

/-- The moduli are pairwise coprime — Lemma C's hypothesis. -/
theorem baseBlocks_coprime (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ((baseBlocks P).map Prod.fst).Pairwise Nat.Coprime := by
  rw [baseBlocks_moduli]
  exact hP.2.1

/-- Every modulus is at least `2` — Lemma A's hypothesis. -/
theorem baseBlocks_two_le (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ c ∈ baseBlocks P, 2 ≤ c.1 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact (hP.2.2 b hb).1

/-- Every height is at least `2`, which is what makes `log H_i > 0` and the allocation
meaningful. -/
theorem baseBlocks_two_le_height (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ c ∈ baseBlocks P, 2 ≤ c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact (hP.2.2 b hb).2.2.1

/-- Every modulus is square-free — Lemma A's hypothesis. -/
theorem baseBlocks_squarefree (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ c ∈ baseBlocks P, Squarefree c.1 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact (hP.2.2 b hb).2.1

/-- Every entry is a ranked block. -/
theorem baseBlocks_rankedBlock (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ c ∈ baseBlocks P, RankedBlock k c.1 c.2.1 c.2.2.1 c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact RankedBlock.of_validRankedSupport k b.1 b.2.2 b.2.1 (hP.2.2 b hb).2.2.2.2

/-- Every support consists of residues — the size count's hypothesis. -/
theorem baseBlocks_support_lt (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ c ∈ baseBlocks P, ∀ s ∈ c.2.1, s < c.1 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact supportFinset_lt_of_valid k b.1 b.2.2 b.2.1 (hP.2.2 b hb).2.2.2.2

/-- The number of vertices of a block is the length of its support list: the `t` of the
exponent formula. -/
theorem baseBlocks_card (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) :
    ∀ b ∈ P, (supportFinset b.2.1).card = b.2.1.length := by
  intro b hb
  exact supportFinset_card b.2.1 (hP.2.2 b hb).2.2.2.2.1

/-- Every block has at least one vertex: a pool's supports are nonempty. Together with
`2 ≤ m` and `2 ≤ k` this is what makes each factor of `stageCard` exceed `1`. -/
theorem baseBlocks_one_le_card (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) : ∀ b ∈ P, 1 ≤ b.2.1.length := by
  intro b hb
  have := hne b hb
  cases hb' : b.2.1 with
  | nil => exact absurd hb' this
  | cons x t => simp

/-! ## The lifted blocks -/

/-- Each lifted block is a ranked block — `lemmaA`, entry by entry. -/
theorem stageBlocks_rankedBlock (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k)
    (hP : ValidPool k P) (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) :
    ∀ c ∈ stageBlocks k P E, RankedBlock k c.1 c.2.1 c.2.2.1 c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hm, hsf, hH, hnb, hv⟩ := hP.2.2 b hb
  exact lemmaA k b.1 hk hm hsf (supportFinset b.2.1) (rankOf b.2.1) b.2.2
    (RankedBlock.of_validRankedSupport k b.1 b.2.2 b.2.1 hv) (E b) (hE b hb)

/-- The lifted moduli are pairwise coprime: powers of pairwise coprime numbers. -/
theorem stageBlocks_coprime (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) : ((stageBlocks k P E).map Prod.fst).Pairwise Nat.Coprime := by
  rw [stageBlocks, List.map_map]
  refine List.pairwise_map.mpr ?_
  exact (List.pairwise_map.mp hP.2.1).imp fun h => Nat.Coprime.pow _ _ h

/-- Every lifted height is positive — Lemma C's fold hypothesis. -/
theorem stageBlocks_height_pos (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) : ∀ c ∈ stageBlocks k P E, 1 ≤ c.2.2.2 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  show 1 ≤ b.2.2 ^ E b
  exact Nat.one_le_pow _ _ (by have := (hP.2.2 b hb).2.2.1; omega)

/-- Every lifted support consists of residues — the counting hypothesis of Lemma C's
fold. -/
theorem stageBlocks_support_lt (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) :
    ∀ c ∈ stageBlocks k P E, ∀ s ∈ c.2.1, s < c.1 := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  intro s hs
  exact ((mem_liftBlock k b.1 (E b) (supportFinset b.2.1) s).mp hs).1

/-- The glued modulus is `stageModulus`. -/
theorem glue_modulus (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) :
    (glueList (stageBlocks k P E)).1 = stageModulus k P E := by
  rw [glueList_fst, stageBlocks, stageModulus, List.map_map]
  rfl

/-- The glued height is `stageHeight`. -/
theorem glue_height (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P) (E : PoolEntry → ℕ) :
    (glueList (stageBlocks k P E)).2.2.2 = stageHeight k P E := by
  rw [glueList_height _ (stageBlocks_height_pos k P hP E), stageBlocks, stageHeight,
    List.map_map]
  rfl

/-- The glued support size is `stageCard` — `glueList_card` and `liftBlock_card`. -/
theorem glue_card (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) : (glueList (stageBlocks k P E)).2.1.card = stageCard k P E := by
  rw [glueList_card _ (stageBlocks_coprime k P hP E) (stageBlocks_support_lt k P E),
    stageBlocks, stageCard, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b hb => ?_)
  have hv := (hP.2.2 b hb).2.2.2.2
  show (liftBlock k b.1 (E b) (supportFinset b.2.1)).card
      = (b.1 ^ (k - 1) * b.2.1.length) ^ E b
  rw [liftBlock_card k b.1 (E b) (supportFinset b.2.1) hk
      (supportFinset_lt_of_valid k b.1 b.2.2 b.2.1 hv),
    supportFinset_card b.2.1 hv.1]

/-- k-th powers come out of a product one factor at a time. -/
private theorem prod_map_pow (k : ℕ) (l : List PoolEntry) (f : PoolEntry → ℕ) :
    (l.map fun b => f b ^ k).prod = (l.map f).prod ^ k := by
  induction l with
  | nil => simp
  | cons b t ih => simp [List.map_cons, List.prod_cons, ih, mul_pow]

/-- The stage modulus is a perfect k-th power, `(Π m_i ^ e_i) ^ k` — Lemma B's hypothesis,
and the reason the exponents carry the factor `k`. -/
theorem stageModulus_eq_pow (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) :
    stageModulus k P E = stageRoot k P E ^ k := by
  rw [stageModulus, stageRoot, ← prod_map_pow k]
  exact congrArg List.prod
    (List.map_congr_left fun b _ => by rw [Nat.mul_comm, pow_mul])

/-- The glued object is a ranked block on `stageModulus` of height `stageHeight`. -/
theorem stage_rankedBlock (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) :
    RankedBlock k (stageModulus k P E) (glueList (stageBlocks k P E)).2.1
      (glueList (stageBlocks k P E)).2.2.1 (stageHeight k P E) := by
  rw [← glue_modulus k P E, ← glue_height k P hP E]
  exact glueList_rankedBlock k (stageBlocks k P E) (stageBlocks_coprime k P hP E)
    (stageBlocks_rankedBlock k P hk hP E hE) (stageBlocks_height_pos k P hP E)

/-! ## Size facts

The positivity the analysis layer needs before it may take logarithms. -/

/-- The stage height is positive: it is `1 + …` in `ℕ`. -/
theorem stageHeight_pos (k : ℕ) (P : List PoolEntry) (E : PoolEntry → ℕ) :
    1 ≤ stageHeight k P E := Nat.le_add_right 1 _

/-- The stage modulus is positive. -/
theorem stageModulus_pos (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) : 0 < stageModulus k P E := by
  refine List.prod_pos ?_
  intro n hn
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
  exact pow_pos (by have := (hP.2.2 b hb).1; omega) _

/-- With every multiplicity positive the stage modulus exceeds `1`, so its logarithm is
positive and the exponent ratio is well formed. -/
theorem one_lt_stageModulus (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) : 1 < stageModulus k P E := by
  obtain ⟨b₀, hb₀⟩ := exists_mem_of_ne_nil P hP.1
  have h1 : ∀ n ∈ P.map fun b => b.1 ^ (k * E b), 1 ≤ n := by
    intro n hn
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hn
    exact Nat.one_le_pow _ _ (by have := (hP.2.2 b hbm).1; omega)
  have hmem : b₀.1 ^ (k * E b₀) ∈ P.map fun b => b.1 ^ (k * E b) :=
    List.mem_map_of_mem hb₀
  refine lt_of_lt_of_le ?_ (List.single_le_prod h1 _ hmem)
  refine Nat.one_lt_pow ?_ (by have := (hP.2.2 b₀ hb₀).1; omega)
  have h2 : 1 ≤ E b₀ := hE b₀ hb₀
  have h3 : 1 * 1 ≤ k * E b₀ := Nat.mul_le_mul hk h2
  omega

/-- With every multiplicity positive the stage height exceeds `1`. -/
theorem one_lt_stageHeight (k : ℕ) (P : List PoolEntry) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) : 1 < stageHeight k P E := by
  obtain ⟨b₀, hb₀⟩ := exists_mem_of_ne_nil P hP.1
  have h0 : ∀ n ∈ P.map fun b => b.2.2 ^ E b - 1, 0 ≤ n := fun _ _ => Nat.zero_le _
  have hmem : b₀.2.2 ^ E b₀ - 1 ∈ P.map fun b => b.2.2 ^ E b - 1 :=
    List.mem_map_of_mem hb₀
  have hle := List.single_le_sum h0 _ hmem
  have h2 : (2 : ℕ) ≤ b₀.2.2 ^ E b₀ := by
    calc (2 : ℕ) ≤ b₀.2.2 := (hP.2.2 b₀ hb₀).2.2.1
      _ = b₀.2.2 ^ 1 := (pow_one _).symm
      _ ≤ b₀.2.2 ^ E b₀ := Nat.pow_le_pow_right (by have := (hP.2.2 b₀ hb₀).2.2.1; omega)
        (hE b₀ hb₀)
  rw [stageHeight]
  omega

/-- The stage support is large: every factor `m_i^{k-1} t_i` is at least `2` once `k ≥ 2`,
`m_i ≥ 2` and the support is nonempty. -/
theorem one_lt_stageCard (k : ℕ) (P : List PoolEntry) (hk : 2 ≤ k) (hP : ValidPool k P)
    (hne : ∀ b ∈ P, b.2.1 ≠ []) (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) :
    1 < stageCard k P E := by
  obtain ⟨b₀, hb₀⟩ := exists_mem_of_ne_nil P hP.1
  have hfac : ∀ b ∈ P, 2 ≤ b.1 ^ (k - 1) * b.2.1.length := by
    intro b hb
    have hm : 2 ≤ b.1 := (hP.2.2 b hb).1
    have ht : 1 ≤ b.2.1.length := baseBlocks_one_le_card k P hP hne b hb
    have hp : 2 ≤ b.1 ^ (k - 1) := by
      calc (2 : ℕ) ≤ b.1 := hm
        _ = b.1 ^ 1 := (pow_one _).symm
        _ ≤ b.1 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (2 : ℕ) ≤ b.1 ^ (k - 1) := hp
      _ = b.1 ^ (k - 1) * 1 := (Nat.mul_one _).symm
      _ ≤ b.1 ^ (k - 1) * b.2.1.length := Nat.mul_le_mul_left _ ht
  have h1 : ∀ n ∈ P.map fun b => (b.1 ^ (k - 1) * b.2.1.length) ^ E b, 1 ≤ n := by
    intro n hn
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hn
    exact Nat.one_le_pow _ _ (by have := hfac b hbm; omega)
  have hmem : (b₀.1 ^ (k - 1) * b₀.2.1.length) ^ E b₀ ∈
      P.map fun b => (b.1 ^ (k - 1) * b.2.1.length) ^ E b := List.mem_map_of_mem hb₀
  refine lt_of_lt_of_le ?_ (List.single_le_prod h1 _ hmem)
  exact Nat.one_lt_pow (by have := hE b₀ hb₀; omega) (by have := hfac b₀ hb₀; omega)

/-! ## The bound on the counting function -/

/-- **The stage, fed to Lemma B.** For every multiplicity vector with all `e_i ≥ 1` and
every word length `L ≥ 1`, the glued stage certifies

`(Π (m_i^{k-1} t_i) ^ e_i) ^ L ≤ D k ((P · H) ^ L)`,

with `P = Π m_i ^ (k e_i)` and `H = 1 + Σ (H_i ^ e_i - 1)`. -/
theorem stage_D_bound (k : ℕ) (P : List PoolEntry) (hk : 1 ≤ k) (hP : ValidPool k P)
    (E : PoolEntry → ℕ) (hE : ∀ b ∈ P, 1 ≤ E b) (L : ℕ) (hL : 1 ≤ L) :
    stageCard k P E ^ L ≤ D k ((stageModulus k P E * stageHeight k P E) ^ L) := by
  have h := lemmaB_card_le_D k (stageRoot k P E) (stageModulus k P E) hk
    (stageModulus_eq_pow k P E)
    (glueList (stageBlocks k P E)).2.1 (glueList (stageBlocks k P E)).2.2.1
    (stageHeight k P E) (stage_rankedBlock k P hk hP E hE) (stageHeight_pos k P E) L hL
  rwa [glue_card k P hk hP E] at h

end KthPower
