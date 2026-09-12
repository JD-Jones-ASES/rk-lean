import RK.Defs

set_option linter.unusedVariables false

/-!
# The two concrete pools

`pool4` and `pool6` of `RK.Defs` are pools in the sense of `ValidPool`: nonempty lists of
blocks `(m, sup, H)` on pairwise coprime square-free moduli `m ≥ 2`, with heights `H ≥ 2`
and each `sup` a ranked support modulo `m` of height `H`.

Everything decidable here is settled by `decide`, in the kernel: the pairwise coprimality
of the moduli, the nonemptiness of the lists, and the per-block ranked-support checks. The
one conjunct that is not decidable as stated is `Squarefree m`, which comes from primality
by `Nat.Prime.squarefree`, the primality itself by `norm_num`.

A per-block check is one pass over the ordered pairs of the support. The largest block is
the `139` block of `pool6`, with `34` vertices and so `34 · 33` ordered pairs, each of which
searches `z < 139` for a sixth-power residue; the smallest is the `5` block of `pool4`,
with `4` vertices.

The blocks are the pinned literals of `Challenge.lean`, re-emitted rather than retyped.
-/

namespace KthPower

set_option maxRecDepth 100000

/-! ## The blocks of `pool4`

One `decide` per block: one pass over the ordered pairs of the support,
checking that a difference which is a nonzero fourth-power residue modulo the
prime forces the rank to drop. -/

/-- The `5` block of `pool4`: 4 vertices, height 4. -/
theorem pool4_block5_valid :
    ValidRankedSupport 4 5
      [(0, 3), (1, 2), (2, 1), (3, 0)] 4 := by
  decide

/-- The `13` block of `pool4`: 7 vertices, height 4. -/
theorem pool4_block13_valid :
    ValidRankedSupport 4 13
      [(0, 0), (2, 2), (5, 1), (7, 2), (8, 0), (10, 1), (12, 3)] 4 := by
  sorry

/-- The `29` block of `pool4`: 12 vertices, height 11. -/
theorem pool4_block29_valid :
    ValidRankedSupport 4 29
      [(0, 7), (1, 6), (2, 5), (3, 2), (5, 9), (6, 8), (14, 10), (15, 9), (16, 3), (17, 0),
       (25, 4), (26, 1)] 11 := by
  sorry

/-- The `37` block of `pool4`: 13 vertices, height 11. -/
theorem pool4_block37_valid :
    ValidRankedSupport 4 37
      [(0, 9), (3, 10), (5, 1), (8, 10), (10, 6), (13, 7), (15, 0), (18, 9), (20, 3), (23, 4),
       (26, 5), (32, 2), (34, 8)] 11 := by
  sorry

/-- The `53` block of `pool4`: 16 vertices, height 8. -/
theorem pool4_block53_valid :
    ValidRankedSupport 4 53
      [(0, 0), (3, 0), (5, 5), (6, 1), (8, 2), (11, 6), (14, 6), (17, 7), (29, 1), (32, 1),
       (35, 2), (37, 3), (38, 2), (40, 7), (41, 4), (43, 7)] 8 := by
  sorry

/-- The `61` block of `pool4`: 16 vertices, height 10. -/
theorem pool4_block61_valid :
    ValidRankedSupport 4 61
      [(0, 1), (4, 6), (7, 7), (14, 4), (17, 5), (24, 2), (27, 3), (31, 7), (35, 9), (37, 1),
       (41, 5), (45, 8), (47, 0), (51, 3), (55, 8), (57, 0)] 10 := by
  sorry

/-- The `101` block of `pool4`: 20 vertices, height 12. -/
theorem pool4_block101_valid :
    ValidRankedSupport 4 101
      [(0, 0), (3, 9), (6, 2), (10, 5), (11, 1), (13, 9), (14, 6), (15, 3), (17, 10), (18, 7),
       (21, 11), (28, 7), (29, 4), (32, 8), (57, 7), (61, 8), (69, 0), (72, 5), (75, 9), (76, 6)] 12 := by
  sorry

/-- The `109` block of `pool4`: 21 vertices, height 8. -/
theorem pool4_block109_valid :
    ValidRankedSupport 4 109
      [(0, 0), (2, 0), (4, 2), (12, 2), (34, 1), (36, 7), (42, 0), (44, 6), (46, 7), (52, 1),
       (54, 4), (62, 6), (71, 5), (76, 3), (84, 1), (86, 4), (88, 5), (94, 4), (95, 3), (101, 0),
       (103, 1)] 8 := by
  sorry

/-! ## The blocks of `pool6`

One `decide` per block: one pass over the ordered pairs of the support,
checking that a difference which is a nonzero sixth-power residue modulo the
prime forces the rank to drop. -/

/-- The `7` block of `pool6`: 6 vertices, height 6. -/
theorem pool6_block7_valid :
    ValidRankedSupport 6 7
      [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)] 6 := by
  sorry

/-- The `19` block of `pool6`: 10 vertices, height 3. -/
theorem pool6_block19_valid :
    ValidRankedSupport 6 19
      [(0, 1), (2, 0), (4, 2), (5, 1), (6, 0), (8, 2), (10, 1), (11, 0), (14, 1), (15, 0)] 3 := by
  sorry

/-- The `31` block of `pool6`: 15 vertices, height 9. -/
theorem pool6_block31_valid :
    ValidRankedSupport 6 31
      [(0, 8), (2, 7), (4, 6), (6, 5), (7, 3), (9, 2), (11, 1), (13, 0), (16, 7), (18, 6),
       (20, 5), (22, 4), (24, 3), (26, 2), (28, 1)] 9 := by
  sorry

/-- The `43` block of `pool6`: 18 vertices, height 6. -/
theorem pool6_block43_valid :
    ValidRankedSupport 6 43
      [(0, 2), (2, 5), (3, 4), (6, 4), (7, 1), (12, 2), (13, 1), (16, 1), (17, 0), (19, 3),
       (22, 3), (23, 0), (25, 5), (26, 1), (31, 1), (36, 3), (37, 0), (40, 2)] 6 := by
  sorry

/-- The `67` block of `pool6`: 23 vertices, height 15. -/
theorem pool6_block67_valid :
    ValidRankedSupport 6 67
      [(0, 5), (2, 8), (4, 14), (5, 9), (6, 1), (10, 11), (11, 2), (14, 3), (16, 3), (18, 12),
       (24, 4), (25, 1), (27, 7), (32, 10), (34, 0), (36, 0), (42, 6), (44, 13), (53, 12),
       (55, 12), (63, 13), (64, 3), (65, 0)] 15 := by
  sorry

/-- The `79` block of `pool6`: 27 vertices, height 17. -/
theorem pool6_block79_valid :
    ValidRankedSupport 6 79
      [(0, 9), (2, 12), (5, 1), (7, 4), (8, 1), (14, 16), (19, 13), (20, 11), (22, 8), (24, 5),
       (25, 2), (30, 0), (36, 14), (37, 12), (39, 15), (42, 3), (44, 7), (45, 1), (49, 13),
       (56, 16), (58, 10), (61, 14), (62, 2), (65, 6), (67, 0), (74, 3), (78, 15)] 17 := by
  sorry

/-- The `103` block of `pool6`: 30 vertices, height 13. -/
theorem pool6_block103_valid :
    ValidRankedSupport 6 103
      [(0, 4), (2, 8), (4, 8), (7, 12), (8, 0), (11, 7), (13, 3), (15, 0), (18, 7), (19, 6),
       (20, 0), (25, 1), (30, 1), (35, 9), (36, 0), (40, 8), (47, 2), (51, 5), (52, 4), (57, 10),
       (62, 10), (63, 1), (67, 11), (68, 0), (78, 6), (83, 5), (85, 2), (88, 11), (90, 6),
       (95, 5)] 13 := by
  sorry

/-- The `127` block of `pool6`: 33 vertices, height 13. -/
theorem pool6_block127_valid :
    ValidRankedSupport 6 127
      [(0, 12), (2, 9), (6, 3), (9, 5), (19, 6), (21, 1), (24, 12), (26, 11), (28, 4), (32, 3),
       (43, 10), (45, 1), (47, 0), (50, 11), (52, 8), (58, 10), (62, 9), (65, 10), (69, 4),
       (71, 0), (81, 1), (84, 7), (86, 6), (88, 1), (91, 11), (93, 2), (98, 11), (99, 7),
       (100, 0), (107, 0), (110, 10), (114, 7), (122, 2)] 13 := by
  sorry

/-- The `139` block of `pool6`: 34 vertices, height 29. -/
theorem pool6_block139_valid :
    ValidRankedSupport 6 139
      [(0, 14), (6, 13), (7, 0), (18, 19), (24, 11), (25, 6), (27, 17), (31, 5), (33, 16),
       (38, 25), (39, 15), (42, 0), (44, 2), (47, 23), (49, 28), (54, 18), (58, 7), (66, 20),
       (67, 3), (74, 24), (79, 10), (85, 9), (91, 8), (93, 21), (96, 0), (104, 3), (110, 1),
       (117, 17), (118, 12), (120, 26), (126, 22), (128, 27), (135, 1), (137, 4)] 29 := by
  decide

/-! ## The two pools

The lengths are part of how the pools are described, and `rfl` settles them. -/

/-- `pool4` has eight blocks. -/
theorem pool4_length : pool4.length = 8 := rfl

/-- `pool6` has nine blocks. -/
theorem pool6_length : pool6.length = 9 := rfl

/-- `pool4` is nonempty. -/
theorem pool4_ne_nil : pool4 ≠ [] := by decide

/-- `pool6` is nonempty. -/
theorem pool6_ne_nil : pool6 ≠ [] := by decide

/-- The eight moduli of `pool4` are pairwise coprime — they are distinct primes. -/
theorem pool4_coprime : (pool4.map Prod.fst).Pairwise Nat.Coprime := by decide

/-- The nine moduli of `pool6` are pairwise coprime — they are distinct primes. -/
theorem pool6_coprime : (pool6.map Prod.fst).Pairwise Nat.Coprime := by decide

/-- **`pool4` is a pool for `k = 4`.** Eight blocks on distinct primes, each modulus
square-free because it is prime, each height at least `2`, and each support a ranked
support of its stated height for fourth powers. -/
theorem pool4_valid_internal : ValidPool 4 pool4 := by
  refine ⟨pool4_ne_nil, pool4_coprime, ?_⟩
  intro b hb
  simp only [pool4, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 5).squarefree, by norm_num,
      pool4_block5_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 13).squarefree, by norm_num,
      pool4_block13_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 29).squarefree, by norm_num,
      pool4_block29_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 37).squarefree, by norm_num,
      pool4_block37_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 53).squarefree, by norm_num,
      pool4_block53_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 61).squarefree, by norm_num,
      pool4_block61_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 101).squarefree, by norm_num,
      pool4_block101_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 109).squarefree, by norm_num,
      pool4_block109_valid⟩

/-- **`pool6` is a pool for `k = 6`.** Nine blocks on distinct primes, each modulus
square-free because it is prime, each height at least `2`, and each support a ranked
support of its stated height for sixth powers. -/
theorem pool6_valid_internal : ValidPool 6 pool6 := by
  refine ⟨pool6_ne_nil, pool6_coprime, ?_⟩
  intro b hb
  simp only [pool6, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 7).squarefree, by norm_num,
      pool6_block7_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 19).squarefree, by norm_num,
      pool6_block19_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 31).squarefree, by norm_num,
      pool6_block31_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 43).squarefree, by norm_num,
      pool6_block43_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 67).squarefree, by norm_num,
      pool6_block67_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 79).squarefree, by norm_num,
      pool6_block79_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 103).squarefree, by norm_num,
      pool6_block103_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 127).squarefree, by norm_num,
      pool6_block127_valid⟩
  · exact ⟨by norm_num, (by norm_num : Nat.Prime 139).squarefree, by norm_num,
      pool6_block139_valid⟩

end KthPower
