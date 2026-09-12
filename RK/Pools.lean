import RK.Defs

/-!
# The two pools, verified block by block

`pool4` and `pool6` are the concrete inputs to the directed construction: nine blocks for `k = 4`,
on the primes `5, 13, 29, 37, 53, 61, 101, 109` and on the composite modulus `51 = 3 · 17`, and
nine for `k = 6`, on the primes `7, 19, 31, 43, 67, 79, 103, 127, 139`. This file proves that each
is a pool in the sense of `ValidPool`, which is the only property of them the construction uses.

`ValidPool k P` has five parts, and each is checked here in the way that suits it:

* `P ≠ []` and the pairwise coprimality of the moduli are finite computations on the stored
  numerals, settled by `decide`;
* `2 ≤ m` and `2 ≤ H` are arithmetic on numerals, settled by `norm_num`;
* `Squarefree m` comes from the factorisation of the modulus: seventeen of the eighteen moduli
  are prime, `norm_num` proves that, and a prime is square-free; the remaining one is `51 = 3·17`,
  square-free because it is a product of two coprime square-free numbers (`squarefree_51`). That
  is the cheap route — the decidability instance for `Squarefree` on `ℕ` runs through
  `Nat.minSqFac`, a factoring search, whereas the primality of a three-digit number is immediate;
* `sup ≠ []` holds by the shape of the stored data: every support is a list literal, so its head
  constructor is a `cons` and `List.cons_ne_nil` closes the goal in each case;
* `ValidRankedSupport k m sup H` — distinct vertices below `m`, ranks below `H`, and a strict
  rank drop along every arc — is one pass over the ordered pairs of the support, with the set of
  nonzero k-th-power residues mod `m` recomputed by a search over `z < m` for each pair. That is
  what `decide` performs in the kernel, and it is done once per block, in the eighteen theorems
  below, so that each block stands as a statement of its own.

The blocks are lower-bound certificates. Nothing here claims that the heights are least possible
or that the supports are largest possible; the theorems say only that these supports carry these
rankings, which is all the exponent needs.
-/

namespace KthPower

set_option maxRecDepth 100000

/-! ## The nine blocks of `pool4`

Each theorem below says: the listed `(vertex, rank)` pairs have distinct vertices below `m`, all
ranks below `H`, and whenever the difference of two vertices is a nonzero fourth-power residue
mod `m`, the rank strictly drops from the first to the second. -/

/-- The block at `m = 5`, height `4`: the four residues `0, 1, 2, 3` ranked in reverse. -/
theorem pool4_block5_valid :
    ValidRankedSupport 4 5 [(0, 3), (1, 2), (2, 1), (3, 0)] 4 := by decide

/-- The block at `m = 13`, height `4`: seven vertices. -/
theorem pool4_block13_valid :
    ValidRankedSupport 4 13 [(0, 0), (2, 2), (5, 1), (7, 2), (8, 0), (10, 1), (12, 3)] 4 := by
  decide

/-- The block at `m = 29`, height `11`: twelve vertices. -/
theorem pool4_block29_valid :
    ValidRankedSupport 4 29
      [(0, 7), (1, 6), (2, 5), (3, 2), (5, 9), (6, 8), (14, 10), (15, 9), (16, 3), (17, 0),
        (25, 4), (26, 1)] 11 := by
  decide

/-- The block at `m = 37`, height `11`: thirteen vertices. -/
theorem pool4_block37_valid :
    ValidRankedSupport 4 37
      [(0, 9), (3, 10), (5, 1), (8, 10), (10, 6), (13, 7), (15, 0), (18, 9), (20, 3), (23, 4),
        (26, 5), (32, 2), (34, 8)] 11 := by
  decide

/-- The block at the composite modulus `m = 51 = 3 · 17`, height `17`: seventeen vertices, the
residue `0` together with the interval `35, …, 50` ranked in reverse. It is the one block of
either pool whose modulus is not prime; square-freeness of the modulus, which is what the
construction needs, is `squarefree_51` below. -/
theorem pool4_block51_valid :
    ValidRankedSupport 4 51
      [(0, 0), (35, 16), (36, 15), (37, 14), (38, 13), (39, 12), (40, 11), (41, 10), (42, 9),
        (43, 8), (44, 7), (45, 6), (46, 5), (47, 4), (48, 3), (49, 2), (50, 1)] 17 := by
  decide

/-- The block at `m = 53`, height `8`: sixteen vertices. -/
theorem pool4_block53_valid :
    ValidRankedSupport 4 53
      [(0, 0), (3, 0), (5, 5), (6, 1), (8, 2), (11, 6), (14, 6), (17, 7), (29, 1), (32, 1),
        (35, 2), (37, 3), (38, 2), (40, 7), (41, 4), (43, 7)] 8 := by
  decide

/-- The block at `m = 61`, height `10`: sixteen vertices. -/
theorem pool4_block61_valid :
    ValidRankedSupport 4 61
      [(0, 1), (4, 6), (7, 7), (14, 4), (17, 5), (24, 2), (27, 3), (31, 7), (35, 9), (37, 1),
        (41, 5), (45, 8), (47, 0), (51, 3), (55, 8), (57, 0)] 10 := by
  decide

/-- The block at `m = 101`, height `12`: twenty vertices. -/
theorem pool4_block101_valid :
    ValidRankedSupport 4 101
      [(0, 0), (3, 9), (6, 2), (10, 5), (11, 1), (13, 9), (14, 6), (15, 3), (17, 10), (18, 7),
        (21, 11), (28, 7), (29, 4), (32, 8), (57, 7), (61, 8), (69, 0), (72, 5), (75, 9),
        (76, 6)] 12 := by
  decide

/-- The block at `m = 109`, height `8`: twenty-one vertices. -/
theorem pool4_block109_valid :
    ValidRankedSupport 4 109
      [(0, 0), (2, 0), (4, 2), (12, 2), (34, 1), (36, 7), (42, 0), (44, 6), (46, 7), (52, 1),
        (54, 4), (62, 6), (71, 5), (76, 3), (84, 1), (86, 4), (88, 5), (94, 4), (95, 3),
        (101, 0), (103, 1)] 8 := by
  decide

/-! ## The nine blocks of `pool6` -/

/-- The block at `m = 7`, height `6`: the six residues `0, …, 5` ranked in reverse. -/
theorem pool6_block7_valid :
    ValidRankedSupport 6 7 [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)] 6 := by decide

/-- The block at `m = 19`, height `3`: ten vertices, the shortest ranking in either pool. -/
theorem pool6_block19_valid :
    ValidRankedSupport 6 19
      [(0, 1), (2, 0), (4, 2), (5, 1), (6, 0), (8, 2), (10, 1), (11, 0), (14, 1), (15, 0)] 3 := by
  decide

/-- The block at `m = 31`, height `9`: fifteen vertices. -/
theorem pool6_block31_valid :
    ValidRankedSupport 6 31
      [(0, 8), (2, 7), (4, 6), (6, 5), (7, 3), (9, 2), (11, 1), (13, 0), (16, 7), (18, 6),
        (20, 5), (22, 4), (24, 3), (26, 2), (28, 1)] 9 := by
  decide

/-- The block at `m = 43`, height `6`: eighteen vertices. -/
theorem pool6_block43_valid :
    ValidRankedSupport 6 43
      [(0, 2), (2, 5), (3, 4), (6, 4), (7, 1), (12, 2), (13, 1), (16, 1), (17, 0), (19, 3),
        (22, 3), (23, 0), (25, 5), (26, 1), (31, 1), (36, 3), (37, 0), (40, 2)] 6 := by
  decide

/-- The block at `m = 67`, height `14`: twenty-three vertices. -/
theorem pool6_block67_valid :
    ValidRankedSupport 6 67
      [(0, 9), (1, 5), (2, 3), (4, 6), (8, 12), (10, 4), (14, 1), (17, 2), (20, 3), (26, 0),
        (30, 10), (33, 11), (37, 13), (39, 0), (43, 11), (46, 12), (47, 8), (49, 13), (55, 9),
        (56, 7), (58, 10), (59, 8), (65, 4)] 14 := by
  decide

/-- The block at `m = 79`, height `17`: twenty-seven vertices. -/
theorem pool6_block79_valid :
    ValidRankedSupport 6 79
      [(0, 9), (2, 12), (5, 1), (7, 4), (8, 1), (14, 16), (19, 13), (20, 11), (22, 8), (24, 5),
        (25, 2), (30, 0), (36, 14), (37, 12), (39, 15), (42, 3), (44, 7), (45, 1), (49, 13),
        (56, 16), (58, 10), (61, 14), (62, 2), (65, 6), (67, 0), (74, 3), (78, 15)] 17 := by
  decide

/-- The block at `m = 103`, height `13`: thirty vertices. -/
theorem pool6_block103_valid :
    ValidRankedSupport 6 103
      [(0, 4), (2, 8), (4, 8), (7, 12), (8, 0), (11, 7), (13, 3), (15, 0), (18, 7), (19, 6),
        (20, 0), (25, 1), (30, 1), (35, 9), (36, 0), (40, 8), (47, 2), (51, 5), (52, 4), (57, 10),
        (62, 10), (63, 1), (67, 11), (68, 0), (78, 6), (83, 5), (85, 2), (88, 11), (90, 6),
        (95, 5)] 13 := by
  decide

/-- The block at `m = 127`, height `9`: thirty-three vertices. -/
theorem pool6_block127_valid :
    ValidRankedSupport 6 127
      [(0, 4), (1, 1), (4, 0), (7, 5), (13, 2), (16, 1), (22, 1), (27, 7), (28, 2), (31, 1),
        (40, 6), (43, 6), (44, 1), (49, 5), (55, 6), (57, 0), (64, 3), (67, 8), (70, 7), (71, 4),
        (79, 3), (84, 6), (85, 2), (86, 0), (92, 0), (97, 8), (99, 4), (101, 0), (106, 7),
        (112, 6), (113, 1), (114, 0), (119, 5)] 9 := by
  decide

/-- The block at `m = 139`, height `22`: thirty-four vertices, the largest block in either pool
and the largest of the eighteen kernel checks. -/
theorem pool6_block139_valid :
    ValidRankedSupport 6 139
      [(0, 16), (1, 11), (5, 19), (11, 12), (20, 1), (25, 14), (30, 2), (31, 0), (40, 12),
        (41, 5), (43, 2), (45, 7), (46, 6), (48, 17), (50, 16), (55, 8), (57, 4), (60, 17),
        (62, 18), (69, 9), (71, 18), (73, 21), (78, 9), (90, 5), (91, 3), (97, 0), (113, 6),
        (115, 14), (116, 13), (117, 10), (118, 4), (128, 16), (129, 15), (138, 20)] 22 := by
  decide

/-! ## The two pools

`pool4.length = 9` and `pool6.length = 9` are stated because the number of blocks is part of how
the pools are described, and `rfl` settles it. -/

/-- `51 = 3 · 17` is square-free: a product of two coprime square-free numbers is square-free,
and `3` and `17` are primes. It is the only modulus in either pool that is not itself prime. -/
theorem squarefree_51 : Squarefree 51 := by
  rw [show (51 : ℕ) = 3 * 17 by norm_num]
  exact Nat.squarefree_mul_iff.mpr
    ⟨by norm_num, (by norm_num : Nat.Prime 3).squarefree,
      (by norm_num : Nat.Prime 17).squarefree⟩

/-- `pool4` has nine blocks. -/
theorem pool4_length : pool4.length = 9 := rfl

/-- `pool6` has nine blocks. -/
theorem pool6_length : pool6.length = 9 := rfl

/-- `pool4` is nonempty. -/
theorem pool4_ne_nil : pool4 ≠ [] := by decide

/-- `pool6` is nonempty. -/
theorem pool6_ne_nil : pool6 ≠ [] := by decide

/-- The nine moduli of `pool4` are pairwise coprime: eight distinct primes and `51 = 3 · 17`,
neither of whose factors is among them. -/
theorem pool4_coprime : (pool4.map Prod.fst).Pairwise Nat.Coprime := by decide

/-- The nine moduli of `pool6` are pairwise coprime — they are distinct primes. -/
theorem pool6_coprime : (pool6.map Prod.fst).Pairwise Nat.Coprime := by decide

/-- **`pool4` is a pool for `k = 4`.** Nine blocks on pairwise coprime square-free moduli — eight
primes and `51 = 3 · 17` — each height at least `2`, and each support a nonempty ranked support
of its stated height for fourth powers. -/
theorem pool4_valid_internal : ValidPool 4 pool4 := by
  refine ⟨pool4_ne_nil, pool4_coprime, ?_⟩
  intro b hb
  simp only [pool4, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 5).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block5_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 13).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block13_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 29).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block29_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 37).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block37_valid⟩
  · exact ⟨by norm_num, squarefree_51, by norm_num,
      List.cons_ne_nil _ _, pool4_block51_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 53).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block53_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 61).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block61_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 101).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block101_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 109).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool4_block109_valid⟩

/-- **`pool6` is a pool for `k = 6`.** Nine blocks on distinct primes, each modulus square-free
because it is prime, each height at least `2`, and each support a nonempty ranked support of its
stated height for sixth powers. -/
theorem pool6_valid_internal : ValidPool 6 pool6 := by
  refine ⟨pool6_ne_nil, pool6_coprime, ?_⟩
  intro b hb
  simp only [pool6, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 7).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block7_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 19).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block19_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 31).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block31_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 43).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block43_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 67).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block67_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 79).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block79_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 103).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block103_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 127).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block127_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 139).squarefree, by norm_num,
      List.cons_ne_nil _ _, pool6_block139_valid⟩

end KthPower
