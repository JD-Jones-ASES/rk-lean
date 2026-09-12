# The mathematics

This document states the theorems proved in this repository and gives the proofs in ordinary
mathematical language. Every numbered Theorem, Lemma and Proposition below is proved in Lean, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, and each step names the Lean
declaration that carries it. Every declaration named here lives in the namespace `KthPower`.

Two kinds of remark are exposition rather than content: the comparisons with the literature (§1,
end, and §8) and the parity discussion of §2 are true but are not what the Lean proves — the Lean
theorems are stated for every `k ≥ 2` with no parity condition. §10 maps the modules to the
sections.

## 1. Definitions and statements

Throughout, `k ≥ 2` is a natural number.

A finite set `A ⊆ ℕ` is **k-th-power-difference-free** if no element of `A` plus a positive k-th
power lies again in `A`: for all `a ∈ A` and all `z ≥ 1`, `a + z^k ∉ A` (`PowerDifferenceFree`).
Stated additively like this, both signs of a difference are covered at once, which is why nothing
below needs an odd-`k` branch. Write

    D_k(N) = max { |A| : A ⊆ {1, …, N}, A k-th-power-difference-free }

(`D`; in Lean a supremum of `Finset.card` over the k-th-power-difference-free members of the
powerset of `Finset.Icc 1 N`).

For a modulus `m ≥ 1`, say that `d` is a **nonzero k-th-power residue** modulo `m` when
`d mod m ≠ 0` and `z^k ≡ d (mod m)` for some `z < m` (`IsNonzeroPowerMod`). The image of
`z ↦ z^k` is taken in full — non-units included; restricting to units would make Lemma A false,
because the leading digit produced there need not be a unit. Write `Q_k(m)` for the set of such
`d`. For `a, b < m`, `diffMod m a b = (b + m − a) mod m` is the residue of `b − a`, computed in `ℕ`
so that every finite claim about a concrete modulus stays decidable (`diffMod`).

A **ranked support** modulo `m` of height `H` is a list `sup` of pairs `(vertex, rank)` with

* pairwise distinct vertices, all `< m`, and all ranks `< H`;
* a strict rank drop along every arc: if `x, y` are vertices with `x ≠ y` and
  `diffMod m x y ∈ Q_k(m)`, then `rank(y) < rank(x)`

(`ValidRankedSupport`, a decidable predicate on the list). The digraph on the vertex set with those
arcs is acyclic, because a ranking that strictly decreases along every arc exists; acyclicity is
not a separate condition, it is what having such a ranking means.

A **pool** for `k` is a nonempty list `P` of blocks `(m, sup, H)` whose moduli are pairwise
coprime, with each `m ≥ 2` square-free, each `H ≥ 2`, and each `sup` a ranked support modulo `m`
of height `H` (`ValidPool`). Writing `t` for the number of vertices of a block, the **exponent of
a pool** is

    alpha k P = ( Σ_i ((k−1) log m_i + log t_i) / log H_i ) / ( 1 + k Σ_i log m_i / log H_i )

(`alpha`).

**Theorem A (the directed construction at every `k`, pointwise form).** Let `k ≥ 2` and let `P` be
a pool for `k`. Then for every real `ρ < alpha k P` one has `N^ρ ≤ D_k(N)` for all sufficiently
large `N`. — `directed_pointwise`.

**Theorem B (liminf form).** Let `k ≥ 2` and let `P` be a pool for `k`. Then

    alpha k P ≤ liminf_{N→∞} log D_k(N) / log N.

— `directed_liminf`.

**Theorem C (the two pools).** The nine blocks of `pool4` listed in `Challenge.lean` form a pool
for `k = 4`, and the nine blocks of `pool6` form a pool for `k = 6`. — `pool4_valid`,
`pool6_valid`.

**Theorem D (the two instances).** `alpha 4 pool4 ≤ liminf log D_4(N)/log N` and
`alpha 6 pool6 ≤ liminf log D_6(N)/log N`. — `fourth_power_liminf`, `sixth_power_liminf`, each
Theorem B applied to Theorem C.

**Theorem E (where the exponents sit).**

    (3 + log 6/log 17)/4 < alpha 4 pool4        and   0.9121 < alpha 4 pool4
    (5 + log 6/log 13)/6 < alpha 6 pool6        and   0.9508 < alpha 6 pool6

— `alpha4_gt_transfer`, `alpha4_gt`, `alpha6_gt_transfer`, `alpha6_gt`. The true values are
`alpha 4 pool4 = 0.912145042700…` and `alpha 6 pool6 = 0.950825559086…`; the two transfer values
are `0.908103119289…` and `0.949759249243…`.

Context. The residue transfer `d_k ≥ (k − 1 + log_m r_k(m))/k` is Ruzsa's [R, Theorem 2], restated
by Younis [Y, Theorem 1.4]; the ranked-block idea at `k = 2` is Krachun's [K]. The two transfer
values compared in Theorem E come from six residues modulo `17` (fourth powers) and six modulo
`13` (sixth powers); `README.md` exhibits both sets and records what is and is not published.
Upper bounds for `D_k(N)` are all `N^{1−o(1)}` [GS, BPPS, Ri], so nothing here is close to the
truth from above.

## 2. What the exponent `k` does, and where parity enters

The Lean statements carry no parity condition, and the proofs below use none. The parity matters
only for whether nonempty pools with arcs exist at all.

The relation `x → y ⇔ diffMod m x y ∈ Q_k(m)` can support a strictly decreasing ranking only if it
is antisymmetric on the block. Modulo a prime `p` with `k ∣ p − 1`, `−1` is a k-th-power residue
exactly when `2k ∣ p − 1`. At **odd** `k`, `−1 = (−1)^k` is always a k-th-power residue, so
`Q_k(m) = −Q_k(m)`, the relation is symmetric, and a block admitting a ranking can have no arcs at
all: it is an independent residue set. Theorem A is still true, but with an independent set its
exponent is `((k−1) log m + log t)/(k log m + log H)`, strictly below the transfer value
`((k−1) log m + log t)/(k log m)`. At **even** `k` the cleanest moduli are the primes with
`k ∣ p − 1` and `2k ∤ p − 1` — `p ≡ 5 (mod 8)` for `k = 4`, `p ≡ 7 (mod 12)` for `k = 6` — where
`Q_k(p) ∩ (−Q_k(p)) = ∅` outright, so every vertex set is acyclic and a block can be both large and
acyclic. Every prime modulus of the two pools is of that kind.

Antisymmetry on the block does not have to come from antisymmetry on all of `ℤ/m`, and one block of
`pool4` shows it need not. If `t ≤ m − max Q_k(m)`, then any `t` consecutive residues form a block:
along the interval order a forward difference lies in `{1, …, t−1}` and a backward one in
`{m−t+1, …, m−1}`, and the latter all exceed `max Q_k(m)`, so every arc runs forward and the
interval order is itself a ranking. `pool4`'s block at `m = 51 = 3 · 17` is this: `Q_4(51) =
{1, 4, 13, 16, 18, 21, 30, 33, 34}` has maximum `34`, so the `17` residues `35, …, 50, 0` form a
block of height `17`. Its modulus is square-free but not prime, and `Q_4(51)` is not antisymmetric
(`18` and `33 = −18` both lie in it) — the interval argument is doing the work, and Theorem A needs
nothing else, since `ValidPool` asks only for square-freeness, coprimality and the ranking.

Inside the proofs, `k` does real work at exactly one place: Step 2 of Lemma A, where the valuation
of a nonzero k-th-power residue is shown to be a multiple of `k`. Everywhere else it is threaded
through unchanged.

## 3. Lemma A: the composite digit lift

Write `digit m j x = ⌊x / m^j⌋ mod m` (`digit`). For a set `S` of residues modulo `m`, a ranking
`h₀` and a multiplicity `e ≥ 1`, put

    liftBlock k m e S  = { x < m^{ke} : digit m (k j) x ∈ S for all j < e }
    liftRank k m e H₀ h₀ x = Σ_{j<e} h₀(digit m (k j) x) · H₀^{e−1−j}

(`liftBlock`, `liftRank`). The lifted block constrains the digits at the `e` positions
`0, k, 2k, …, k(e−1)` and leaves the other `e(k−1)` positions free; the lifted ranking reads the
ranks of the constrained digits as a base-`H₀` numeral, lowest position most significant.

**Lemma A.** Let `m ≥ 2` be square-free, `k ≥ 1`, and let `S` with ranking `h₀` be a block modulo
`m` of height `H₀`. Then for every `e ≥ 1`, `liftBlock k m e S` with ranking `liftRank k m e H₀ h₀`
is a block modulo `m^{ke}` of height `H₀^e`. — `lemmaA`.

**Lemma A′ (its size).** If every element of `S` is `< m`, then
`|liftBlock k m e S| = (m^{k−1} |S|)^e`. — `liftBlock_card`, by induction on `e` with the
digit-shift identity `digit_add_pow` and the base count `base_count`.

*Proof of Lemma A.* Let `x ≠ y` be elements of the lifted block and suppose
`d := diffMod (m^{ke}) x y ∈ Q_k(m^{ke})`. From the definition of `Q_k` one extracts once and for
all a witness `z ≠ 0`, `z < m^{ke}`, and a `λ` with `z^k = d + λ m^{ke}`
(`exists_lambda_of_isNonzeroPowerMod`). Let `r` be the least base-`m` position at which `x` and `y`
differ; it exists and `r < ke` (`exists_least_digit_ne`). The argument is six steps.

| Step | Statement | Lean |
| --- | --- | --- |
| 0 | `m^r ∣ d` and `m^{r+1} ∤ d`, i.e. `r = v_m(d)`; the wraparound term `κ m^{ke}` does not disturb this because `r < ke` | `step0_exact_dvd` |
| 1 | `δ := digit m r d = diffMod m (digit m r x) (digit m r y)`: the `r`-th digit of the difference is the difference of the `r`-th digits, with no borrow, because the positions below `r` agree and those above contribute multiples of `m` | `step1_leading_digit` |
| 2 | `k ∣ r` | `step2_dvd` |
| 3 | with `r = k j`, `m^j ∣ z` | `step3_pow_dvd` |
| 4 | `δ ∈ Q_k(m)`: the leading digit is a nonzero k-th-power residue modulo `m` | `step4_leading_power` |
| 5 | `liftRank … y < liftRank … x` | `step5_rank_drop` |

Step 2 is where `k` and square-freeness are both spent. For each prime `q ∣ m` there are two
cases. If `v_q(z) < e` (an *uncapped* coordinate) then `v_q(λ m^{ke}) ≥ ke > k v_q(z) = v_q(z^k)`,
so the k-th-power term dominates the sum `z^k = d + λ m^{ke}` and `v_q(d) = k v_q(z)`, a multiple
of `k` (`step2_uncapped`, via the dominated-term lemma `padicValNat_add_of_lt`). If `v_q(z) ≥ e`
(a *capped* coordinate) then both terms are divisible by `q^{ke}` and `v_q(d) ≥ ke`
(`step2_capped`). Square-freeness makes `v_m(d)` the minimum of the `v_q(d)` over `q ∣ m`
(`pow_dvd_iff_forall_prime`) and makes that minimum attained exactly (`exists_padicValNat_eq`);
since `r = v_m(d) < ke`, the minimum is attained at an uncapped coordinate, so `r = k v_q(z)` for
that `q`, and `k ∣ r`. The hypothesis cannot be dropped: at `m = 9`, `k = 2`, `d = 9` has
`v_m(d) = 1`.

Step 3 reassembles: writing `r = k j`, every coordinate has `v_q(z) ≥ j` — uncapped ones because
`k v_q(z) = v_q(d) ≥ k j`, capped ones because `v_q(z) ≥ e > j` — and square-freeness turns the
per-prime bounds back into `m^j ∣ z` (`pow_dvd_iff_forall_prime` again).

Step 4 writes `z = m^j u` and divides: `d / m^{kj} ≡ u^k (mod m^{k(e−j)})`, so
`δ = digit m (kj) d ≡ u^k (mod m)`, and `δ ≠ 0` by Step 0, which is exactly `δ ∈ Q_k(m)`.

Step 5 is the geometric assembly. By Step 1 and `δ ∈ Q_k(m)`, the block hypothesis on `S` gives
`h₀(digit m (kj) y) < h₀(digit m (kj) x)`, a drop of at least one unit at the constrained position
`j`; the positions below `j` carry equal digits (`liftRank_split`), and the whole tail above
contributes less than `H₀^{e−1−j}` because each of its terms is `< H₀` and the weights are a
geometric series (`liftRank_tail_lt`, from `sum_coeff_lt_pow` / `sum_reflect_lt_pow`). So the drop
at position `j` dominates and the lifted rank strictly decreases. Ranks stay below `H₀^e` by
`liftRank_lt_pow`, and the vertices are `< m^{ke}` by construction. ∎

## 4. Lemma B: from a block to integers

Let `P` be a modulus, `C` a block modulo `P` with ranking `h` of height `H`, and `L ≥ 1`. Put

    wordBlock P L C = { X < P^L : digit P j X ∈ C for all j < L }
    wordRank P L H h X = Σ_{j<L} h(digit P j X) · H^{L−1−j}
    integerSet P L H C h = { X + P^L · wordRank P L H h X + 1 : X ∈ wordBlock P L C }

(`wordBlock`, `wordRank`, `integerSet`; the `+1` puts the set in `[1, (PH)^L]` rather than starting
at `0`).

**Lemma B.** If `P = n^k` for some `n` and `k ≥ 1`, and `C` with `h` is a block modulo `P` of
height `H`, then for every `L ≥ 1` the set `integerSet P L H C h` is k-th-power-difference-free
(`lemmaB_pdf`), is contained in `[1, (PH)^L]` (`integerSet_subset`), and has `|C|^L` elements
(`integerSet_card`).

*Proof.* Suppose `a` and `a + z^k` both lie in the set, `z ≥ 1`, coming from words `X` and `Y`.
Reducing modulo `P^L` kills the displacement (`word_mod_pow`), so `z^k ≡ Y − X (mod P^L)`; and
`X ≠ Y`, since `X = Y` would force `a = a + z^k`. Let `j < L` be the least position where they
differ (`exists_least_digit_ne_of_lt`). The steps mirror §3, and are simpler:

| Step | Statement | Lean |
| --- | --- | --- |
| 0 | `P^j` divides `Y − X` exactly: `Y − X = P^j(δ + P·Z)` | `word_step0_exact_dvd` |
| 1 | `δ = digit P j Y − digit P j X`, no borrow from below `j` | `word_step1_leading_digit` |
| 2 | `P^j ∣ z^k` | `word_step2_pow_dvd_pow` |
| 3 | `z^k = P^j u^k` for some `u` | `word_step3_root_split` |
| 4 | `δ ∈ Q_k(P)` | `word_step4_leading_power` |
| 5 | `wordRank … Y < wordRank … X` | `word_step5_rank_drop` |

Step 3 is where the perfect-k-th-power hypothesis is used and is the whole of the exponent's role
here: `P^j = (n^j)^k`, so `(n^j)^k ∣ z^k` gives `n^j ∣ z` by `Nat.pow_dvd_pow_iff` (`k ≠ 0`), for
*every* natural `n` — no primality and no square-freeness. Step 5 is the same geometric argument
as Step 5 of Lemma A. Its consequence closes the argument: from `wordRank Y < wordRank X` and
`Y < P^L` one gets `Y + P^L · wordRank Y < X + P^L · wordRank X` (`integerSet_lt_of_rank_lt`),
because dropping the rank by one unit removes a whole `P^L`, which the residual `Y` cannot make
up. So `a + z^k < a`, which is absurd. Hence no such pair exists.

The containment is `X < P^L` together with `wordRank < H^L` (`wordRank_lt_pow`), and the
cardinality is `|wordBlock| = |C|^L` (`wordBlock_card`, by induction on `L`) transported through
the injection `wordEmbed_injOn`.

**Lemma B′ (the link to the counting function).** A k-th-power-difference-free subset of `{1, …, N}`
is a competitor in the supremum defining `D_k(N)`, so its size bounds `D_k(N)` below
(`le_D_of_pdf`); combining, for `P = n^k` and a block `C` of height `H ≥ 1`,

    |C|^L ≤ D_k((P H)^L)    for every L ≥ 1.

— `lemmaB_card_le_D`. This single inequality is everything the exponent arithmetic consumes.

## 5. Lemma C: the Chinese-remainder glue

For coprime `P, Q` put `crtBlock P Q Cp Cq = { x < PQ : x mod P ∈ Cp, x mod Q ∈ Cq }`
(`crtBlock`).

**Lemma C.** If `Cp` with `hp` is a block modulo `P` of height `Hp ≥ 1` and `Cq` with `hq` a block
modulo `Q` of height `Hq ≥ 1`, and `P, Q` are coprime, then `crtBlock P Q Cp Cq` with the ranking
`x ↦ hp(x mod P) + hq(x mod Q)` is a block modulo `PQ` of height `Hp + Hq − 1`, and
`|crtBlock P Q Cp Cq| = |Cp| · |Cq|`. — `lemmaC`, `crtBlock_card`.

*Proof.* A k-th power modulo `PQ` reduces to a k-th power modulo `P` and one modulo `Q`
(`exists_pow_mod_of_dvd`), each of which may be zero or nonzero, and a difference reduces to a
difference (`diffMod_mod_of_dvd`). Given `x ≠ y` in the glued block with
`diffMod (PQ) x y ∈ Q_k(PQ)`, at least one coordinate difference is nonzero (`coord_ne_zero`); a
zero coordinate leaves its summand unchanged (`coord_rank_le`) and a nonzero one strictly decreases
it (`coord_rank_lt`), so the sum strictly decreases. Ranks land below `Hp + Hq − 1` by
`crtRank_lt`, and the cardinality is the Chinese remainder bijection (`crt_injOn`, `crt_image`).
Nothing in this lemma depends on `k` beyond threading it through `Q_k`; in particular no
perfect-k-th-power hypothesis appears here — the caller keeps the glued modulus a perfect k-th
power. ∎

**The fold.** Blocks are carried as tuples `Block = (modulus, support, ranking, height)`
(`Block`), with `trivialBlock = (1, {0}, 0, 1)` as the unit and `glueTwo` one step of Lemma C;
`glueList l = l.foldr glueTwo trivialBlock` (`glueList`). Along a list of blocks with pairwise
coprime moduli, the modulus is the product (`glueList_fst`), the height is `1 + Σ (H_i − 1)`
(`glueList_height`), the support size is `Π |C_i|` (`glueList_card`), and the result is a block
(`glueList_rankedBlock`).

## 6. The stage, and its bound on `D_k`

Let `P` be a pool and `E` a multiplicity for each entry. The blocks of the pool
(`baseBlocks`, with the pool conditions read off `ValidPool` once in `baseBlocks_coprime`,
`baseBlocks_squarefree`, `baseBlocks_rankedBlock`, `baseBlocks_card` and their neighbours) are
lifted by Lemma A (`stageBlocks`) and glued by Lemma C. The three closed forms are

    stageRoot    = Π_i m_i^{e_i}
    stageModulus = Π_i m_i^{k e_i}   ( = stageRoot^k,  stageModulus_eq_pow )
    stageCard    = Π_i (m_i^{k−1} t_i)^{e_i}
    stageHeight  = 1 + Σ_i (H_i^{e_i} − 1)

(`stageRoot`, `stageModulus`, `stageCard`, `stageHeight`), and `glue_modulus`, `glue_height`,
`glue_card` identify them with the modulus, height and support size of the glued block; the glued
object is a block (`stage_rankedBlock`).

**Proposition F (the stage bound).** For `k ≥ 1`, a pool `P`, multiplicities `e_i ≥ 1` and every
`L ≥ 1`,

    stageCard^L ≤ D_k( (stageModulus · stageHeight)^L ).

— `stage_D_bound`: `stageModulus` is the perfect k-th power `stageRoot^k`, so Lemma B′ applies to
the glued block. The multiplicity travels as a function of the pool entry rather than as an
indexed vector, which is why every closed form above is a `List.map` over the pool and the
logarithms below are a sum exchange rather than an induction.

## 7. The allocation and the limit

Write `stageExponent = log stageCard / log (stageModulus · stageHeight)` (`stageExponent`), and

    alphaNum k P = Σ_i log(m_i^{k−1} t_i) / log H_i,     alphaDen k P = 1 + k Σ_i log m_i / log H_i

(`alphaNum`, `alphaDen`). Since `(k−1) log m + log t = log(m^{k−1} t)` blockwise
(`log_natPow_mul`), `alpha k P = alphaNum / alphaDen` (`alpha_eq_ratio`), and the denominator is
`≥ 1` (`alphaDen_pos`).

**Proposition G (the limit).** For a pool with no empty support, with the allocation
`e_i(U) = ⌊U / log H_i⌋` (`alloc`),

    stageExponent k P (alloc U) → alpha k P   as U → ∞.

— `tendsto_stageExponent`.

*Proof.* Every `H_i ≥ 2`, so `log H_i > 0` (`logHeight_pos`) and `bigLog P = Σ_i log H_i` dominates
each of them (`logHeight_le_bigLog`); for `U ≥ bigLog P` every `e_i(U) ≥ 1` (`one_le_alloc`). By
the floor bounds, `e_i(U) log H_i ∈ (U − log H_i, U]` (`alloc_mul_logHeight_le`,
`sub_logHeight_lt_alloc_mul`). Hence

    log stageModulus = k Σ_i e_i log m_i = k Σ_i (log m_i / log H_i)(U + O(1))
    log stageCard    =   Σ_i e_i log(m_i^{k−1} t_i) =  Σ_i (log(m_i^{k−1} t_i)/log H_i)(U + O(1))

(`log_stageModulus`, `log_stageCard`, both a `log`-of-product exchange, `log_natProd`), and the
height is sandwiched between `max_i H_i^{e_i}` and `ℓ · max_i H_i^{e_i}` for `ℓ = |P|`
(`pow_height_le_stageHeight`, `stageHeight_le_of_forall_le`), giving

    U − bigLog P ≤ log stageHeight ≤ U + log ℓ

(`log_stageHeight_lower`, `log_stageHeight_upper`). So numerator and denominator are both
`Θ(U)` with *additive* `O(1)` errors, and the ratio converges to `alphaNum / alphaDen = alpha k P`
(`tendsto_ratio_of_abs_sub_le`, `tendsto_div_atTop_of_abs_sub_le`, with the error bookkeeping in
`abs_sum_map_sub_le`, `abs_ratio_mul_le`, `abs_alloc_weighted_sub_le`). ∎

**Corollary H.** For `ρ < alpha k P` there is a multiplicity vector with every `e_i ≥ 1`,
`stageModulus · stageHeight > 1`, and `ρ < stageExponent`. — `exists_stage_exponent_gt`.

## 8. The passage to every `N`, and the liminf

**Proposition I (the passage, with the stage abstracted away).** Let `B, C ≥ 2` be naturals with
`C^L ≤ D_k(B^L)` for every `L ≥ 1`, and let `ρ < log C / log B`. Then `N^ρ ≤ D_k(N)` for all
sufficiently large `N`. — `passage` (a private lemma of `RK/Asymptotics.lean`).

*Proof.* Put `α = log C / log B` and `L = ⌊log N / log B⌋`, so that `B^L ≤ N < B^{L+1}`. Then
`D_k(N) ≥ D_k(B^L) ≥ C^L = B^{αL} ≥ N^α / B^α` — the first inequality by monotonicity of `D_k`
(`D_mono`), the last because `N < B^{L+1}`. The constant factor `B^{−α}` is absorbed because
`N^{α−ρ} → ∞`, and that absorption is exactly where `ρ < α` is spent. ∎

Combining Proposition F (at `B = stageModulus · stageHeight`, `C = stageCard`) with Corollary H
and Proposition I gives Theorem A for a pool with no empty support (`stage_pointwise`,
`pointwise_of_ne_nil`), and §9 removes that proviso, yielding `pointwise_internal` — Theorem A.

Theorem B follows. The sequence `u_N = log D_k(N) / log N` satisfies `u_N ≤ 1` for `N ≥ 2`, since
`D_k(N) ≤ N` (`D_le`), so it is cobounded above; for each `ρ < alpha k P`, Theorem A gives
`u_N ≥ ρ` eventually, hence `ρ ≤ liminf u`, and letting `ρ ↑ alpha k P` gives
`alpha k P ≤ liminf u` (`liminf_internal`). The boundedness step is not decoration: without it
`Filter.le_liminf_of_le` does not apply.

## 9. The empty-support normalisation

`ValidPool` does not forbid an empty support list: the three conditions of a ranked support are
vacuous on the empty list, so `(m, [], H)` is a legal block. The counting argument, however, wants
every block to have a vertex — `liftBlock_card` and the positivity facts `one_lt_stageCard` all
read `|C| ≥ 1`. Normalising is harmless:

    fixEntry (m, sup, H) = if sup = [] then (m, [(0,0)], H) else (m, sup, H),    fixPool = map fixEntry

(`fixEntry`, `fixPool`). The single vertex `0` at rank `0` is a ranked support modulo any `m ≥ 2`
of any height `H ≥ 2` — there is one vertex, so the arc condition is vacuous — and the moduli and
heights are untouched, so `fixPool P` is again a pool (`fixPool_valid`) with no empty support
(`fixPool_sup_ne_nil`). It has the same exponent: the only quantity that moves is `log t` at a
block with `t = 0`, and in Mathlib's convention `Real.log 0 = 0 = Real.log 1`
(`alpha_fixPool`). Theorem A for a general pool is therefore Theorem A for `fixPool P`.

This is the one place where a Mathlib convention is load-bearing, and it is load-bearing in the
harmless direction: a block with no vertices contributes nothing either way.

## 10. The numeric layer

`alpha k P` is a ratio of sums of ratios of logarithms. No floating-point or interval arithmetic
appears anywhere in the development. The one idea is that a rational bound on a ratio of
logarithms *is* a comparison of two natural numbers: for `a, b ≥ 2` and `q ≥ 1`,

    p/q < log a / log b   ⟺   b^p < a^q,        log a / log b < p/q   ⟺   a^q < b^p,

because `log b > 0` and `log` is strictly monotone (`lt_log_div_log`, `log_div_log_lt`). Each such
comparison is discharged by `decide`, i.e. by the kernel's own arbitrary-precision arithmetic on
`Nat.pow` and `Nat.decLt`; the largest pair here is `22^3494` (4691 digits) against
`1764220719766^383`, and all thirty-eight comparisons together cost a small part of the module's
elaboration. Because `decide` is more kernel-bound than `norm_num`, not less, this strengthens the
trust posture rather than relaxing it.

Unfolding the pool folds once (`alpha4_eq`, `alpha6_eq`, using the eighteen identities
`logNum4_*`, `logNum6_*` that merge `(k−1) log m + log t` into `log(m^{k−1} t)`) puts each exponent
in the shape

    alpha = ( Σ_i log a_i / log H_i ) / ( 1 + k Σ_i log m_i / log H_i ),    a_i = m_i^{k−1} t_i,

so a lower bound needs a rational lower bound `ρ_i` for each `log a_i / log H_i` and a rational
upper bound `σ_i` for each `log m_i / log H_i`; then `alpha ≥ (Σ ρ_i)/(1 + k Σ σ_i)`, a rational
number, and the assembly is `norm_num` and `linarith` on small numbers
(`alpha4_gt_rational`, `alpha6_gt_rational`). Each `ρ_i`, `σ_i` below is a best rational
approximation with denominator at most `400`.

**`k = 4`** (`logLo4_*`, `logHi4_*`):

| `m` | `t` | `H` | `a = m³t` | `ρ`: `log a / log H >` | `σ`: `log m / log H <` |
| --- | --- | --- | --- | --- | --- |
| 5 | 4 | 4 | 500 | 1179/263 | 238/205 |
| 13 | 7 | 4 | 15379 | 1370/197 | 420/227 |
| 29 | 12 | 11 | 292668 | 1454/277 | 521/371 |
| 37 | 13 | 11 | 658489 | 2017/361 | 128/85 |
| 51 | 17 | 17 | 2255067 | 253/49 | 501/361 |
| 53 | 16 | 8 | 2382032 | 346/49 | 758/397 |
| 61 | 16 | 10 | 3631696 | 2401/366 | 341/191 |
| 101 | 20 | 12 | 20606020 | 1735/256 | 743/400 |
| 109 | 21 | 8 | 27195609 | 2091/254 | 837/371 |

**`k = 6`** (`logLo6_*`, `logHi6_*`):

| `m` | `t` | `H` | `a = m⁵t` | `ρ`: `log a / log H >` | `σ`: `log m / log H <` |
| --- | --- | --- | --- | --- | --- |
| 7 | 6 | 6 | 100842 | 1749/272 | 366/337 |
| 19 | 10 | 3 | 24760990 | 4587/296 | 729/272 |
| 31 | 15 | 9 | 429437265 | 3284/363 | 497/318 |
| 43 | 18 | 6 | 2646151974 | 1889/156 | 254/121 |
| 67 | 23 | 14 | 31052877461 | 2609/285 | 615/386 |
| 79 | 27 | 17 | 83080522773 | 1837/207 | 566/367 |
| 103 | 30 | 13 | 347782222290 | 1637/158 | 468/259 |
| 127 | 33 | 9 | 1090266190431 | 4453/353 | 657/298 |
| 139 | 34 | 22 | 1764220719766 | 3494/383 | 265/166 |

The two transfer values are handled the same way, from above: `log 6 / log 17 < 117/185`
(`logHi_transfer4`), so `(3 + log 6/log 17)/4 < 168/185 = 0.908108108108…`, and
`log 6 / log 13 < 146/209` (`logHi_transfer6`), so `(5 + log 6/log 13)/6 < 397/418 =
0.949760765550…`.

Assembling, the rational lower bounds proved are

    alpha 4 pool4 > 0.912120556433…      (true value 0.912145042700…)
    alpha 6 pool6 > 0.950819216434…      (true value 0.950825559086…)

which clear the decimal targets `0.9121` and `0.9508` by `2.06 × 10⁻⁵` and `1.92 × 10⁻⁵`, and the
two rational transfer ceilings by `4.01 × 10⁻³` and `1.06 × 10⁻³`. The roundings therefore cost
about `2.4 × 10⁻⁵` of the `4.5 × 10⁻⁵` available above `0.9121`, and `6.3 × 10⁻⁶` of the
`2.6 × 10⁻⁵` available above `0.9508`; tightening any bound means replacing
four numbers on one line, since each lemma is one translation plus one kernel comparison.
`scripts/check_blocks.py` recomputes the exponents, re-checks every one of the thirty-eight power
comparisons as an exact integer comparison, and redoes the rational assembly, independently of
Lean.

## 11. The two pools, as finite checks

`ValidPool k P` has four parts, each checked in the way that suits it (`RK/Pools.lean`):
non-emptiness and pairwise coprimality of the moduli are computations on the stored numerals,
settled by `decide`; `m ≥ 2` and `H ≥ 2` are `norm_num`; `Squarefree m` is read off the
factorisation — for the seventeen prime moduli from primality, which `norm_num` proves and which
implies square-freeness, and for `51 = 3 · 17` from the two distinct prime factors; either route is
cheaper than the decidability instance for `Squarefree`, which factors by search. Finally
`ValidRankedSupport k m sup H` is one pass over the ordered pairs of the support with `Q_k(m)`
recomputed by a search over `z < m`, which is what `decide` performs in the kernel. This is done
once per block, so each of the eighteen blocks stands as a statement of its own:
`pool4_block5_valid … pool4_block109_valid`, `pool6_block7_valid … pool6_block139_valid`. The
largest is the 34-vertex support at `139`.

The blocks are lower-bound witnesses. Nothing here claims that a support is largest possible or
that a height is least possible.

## 12. Modules and sections

| Module | Sections |
| --- | --- |
| `RK/Defs.lean` | §1 (the nine definitions, generated from `Challenge.lean`) |
| `RK/DiffMod.lean` | §1 (`diffMod`), and the `λ`-decomposition used at the start of §3 |
| `RK/RankedBlocks.lean` | §1: the functional form `RankedBlock` and the list-to-`Finset` bridge |
| `RK/LemmaA.lean` | §3 |
| `RK/LemmaB.lean` | §4 |
| `RK/LemmaC.lean` | §5 |
| `RK/Construction.lean` | §6 |
| `RK/Asymptotics.lean` | §7, §8, §9 |
| `RK/Pools.lean` | §11 |
| `RK/Numeric.lean` | §10 |
| `RK/Main.lean` | the ten targets, assembled |
| `Solution.lean` | the ten statements of `Challenge.lean`, restated verbatim |

Where the Lean reaches a statement by a different route than the prose above, the module's own
header says so.

## References

* [BPPS] A. Balog, J. Pelikán, J. Pintz, E. Szemerédi, *Difference sets without κ-th powers*,
  Acta Math. Hungar. **65** (1994), no. 2, 165–187, doi:10.1007/BF01874311.
* [BG] R. Beigel, W. Gasarch, *Square-Difference-Free Sets of Size Ω(n^{0.7334…})*,
  arXiv:0804.4892.
* [GS] B. Green, M. Sawhney, *New bounds for the Furstenberg–Sárközy theorem*, arXiv:2411.17448.
* [GGTW] B. Georgiev, J. Gómez-Serrano, T. Tao, A. Z. Wagner, *Mathematical exploration and
  discovery at scale*, arXiv:2511.02864 (Problem 6.31).
* [K] D. Krachun, *Square-Difference-Free Sets beyond the Three-Quarter Barrier*,
  arXiv:2608.01325 (2 Aug 2026).
* [Le] M. Lewko, *An improved lower bound related to the Furstenberg–Sárközy theorem*,
  Electron. J. Combin. **22** (2015), no. 1, P1.32, doi:10.37236/4656.
* [Lo] L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory **25** (1979),
  no. 1, 1–7, doi:10.1109/TIT.1979.1055985 (cited in `README.md` as context only).
* [R] I. Z. Ruzsa, *Difference sets without squares*, Period. Math. Hungar. **15** (1984), no. 3,
  205–209, doi:10.1007/BF02454169.
* [Ri] A. Rice, *A maximal extension of the best-known bounds for the Furstenberg–Sárközy
  theorem*, Acta Arith. **187** (2019), no. 1, 1–41, doi:10.4064/aa170828-26-8.
* [S] A. Sárközy, *On difference sets of sequences of integers. I*, Acta Math. Acad. Sci. Hungar.
  **31** (1978), no. 1–2, 125–149, doi:10.1007/BF01896079.
* [Y] K. Younis, *Lower bounds in the polynomial Szemerédi theorem*, arXiv:1908.06058
  (Theorem 1.4 is the general-k transfer).
