# Verification

What was checked at this snapshot, and how to repeat it. The statements under check are the ten
theorems of `Challenge.lean`; everything else in this repository exists to prove them unchanged.

## Toolchain

* Lean `leanprover/lean4:v4.33.0` (`lean-toolchain`).
* Mathlib pinned in `lake-manifest.json` at `db584cd6d46c92f209a44c0f1c829460d327499d`
  (tag `v4.33.0`), with its own dependencies at the revisions the manifest records.
* No `lake update` is ever run; `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are not
  edited. A dependency change would be a deliberate, reviewed commit.

## Build

```sh
lake exe cache get
lake build
```

`lake build` compiles the four default targets: the library `RK`, `Challenge`, `Solution` and
`Test`. Expected outcome: `Challenge.lean` reports **ten** `declaration uses sorry` warnings — one
per pinned theorem, its placeholders, by design — and nothing else warns or errors.

At this snapshot `lake build` completed exactly as described above, in `<<BUILD_TIME>>` with the
Mathlib cache in place (wall-clock time depends on the machine and on the state of the cache);
`RK/`, `Solution.lean` and `Test/` contain no `sorry`, which `scripts/check-source.py` enforces
independently.

## Axioms

`Test/Axioms.lean` walks every constant in the environment whose name begins with `KthPower.`,
`_private.RK.` or `_private.Solution.` and collects the axioms it depends on; the build fails
(via `logError`) if any axiom outside `propext`, `Classical.choice`, `Quot.sound` appears.
`Challenge.lean` is not imported there, so its placeholders are outside the audit's reach by
construction rather than by exclusion. The audit also fails if it matches fewer than
`<<AUDIT_FLOOR>>` constants — so a renamed namespace cannot make it pass vacuously — or if any of
the ten compared theorems is missing from the environment: `directed_liminf`,
`directed_pointwise`, `pool4_valid`, `pool6_valid`, `alpha4_gt_transfer`, `alpha4_gt`,
`alpha6_gt_transfer`, `alpha6_gt`, `fourth_power_liminf`, `sixth_power_liminf`, all in
`KthPower`.

At this snapshot the audit reported (reproduce with `lake build Test`; the line is logged by
`Test/Axioms.lean`):

```
Audited <<AUDIT_COUNT>> project constants; unexpected axiom dependencies: 0.
```

**Non-default options.** The development sets, in total: `autoImplicit false` and
`relaxedAutoImplicit false` for every module (`lakefile.toml`); `linter.unusedVariables false` in
eight modules, so that the standing hypotheses a step lemma carries for readability do not raise
warnings when its proof does not consume them; `maxRecDepth 10000` in `RK/Construction.lean` and
`RK/Numeric.lean`, `maxRecDepth 100000` in `RK/Pools.lean`; and
`exponentiation.threshold 100000` in `RK/Numeric.lean`, whose default of `256` is an evaluation
guard that the power comparisons there exceed — without it the kernel-backed `decide`s still
succeed but each logs a threshold warning. Every one of these raises an elaboration limit or
silences a linter; none affects the kernel check.

**Tactics on the finite and numeric parts.** The seventeen block verifications of `RK/Pools.lean`
and the thirty-six power comparisons of `RK/Numeric.lean` use ordinary `decide`, which hands the
proposition to the kernel's own arbitrary-precision arithmetic. There is no `decide +kernel` and
no `native_decide` anywhere in the repository, and no custom `axiom`. The largest finite check is
the 34-vertex support at modulus `139`, which is `33 · 34` ordered pairs each testing membership
in the set of nonzero sixth-power residues by a search over `z < 139`; it elaborates in
`<<DECIDE_TIME_139>>`. The largest power comparison is `29^2931 < 1764220719766^350`, two numbers
of 4287 decimal digits each.

**Mutation controls run at this snapshot:** `<<MUTATION_CONTROLS>>`. The faults injected are a
corrupted vertex and a corrupted rank in one block of each pool (the corresponding `decide` must
report the proposition false), a modulus replaced by a non-square-free number (leaving an
unprovable goal), one rational bound loosened past the true ratio (the natural-power comparison
must fail), and a `sorry` injected into a proved module of `RK/` (which compiles silently through
`Solution.lean` and must be caught by the axiom audit and by the source guard).

## Source guard

```sh
python3 scripts/check-source.py
```

rejects `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`, `implemented_by`,
`extern`, `Lean.ofReduceBool` and the kernel-bypass options `debug.skipKernelTC` and
`debug.byAsSorry` outside comments and strings in `RK/*.lean`, `RK.lean`, `Solution.lean`,
`Test.lean` and `Test/*.lean`. `Challenge.lean` is checked only for the two kernel-bypass options:
its placeholders are intentional. It prints the number of files checked and exits `0` on success,
`1` with a `file:line: prohibited proof token` report otherwise.

## Statement identity

`Challenge.lean` and `Solution.lean` declare the same ten theorem names in the namespace
`KthPower`, with the same statements, over the same nine definitions (`IsNonzeroPowerMod`,
`diffMod`, `ValidRankedSupport`, `ValidPool`, `alpha`, `PowerDifferenceFree`, `D`, `pool4`,
`pool6`). The `def` commands of `RK/Defs.lean` are character-for-character those of the Challenge,
including the two decidability instances; `RK/Defs.lean` is generated from `Challenge.lean` and is
not edited by hand. Checked by printing each definition and the type of each theorem with
`pp.explicit` from `import Challenge` and from `import Solution` and comparing the outputs:
identical. `Solution.lean` does not import `Challenge.lean`.

To repeat: run `lake env lean` on a scratch file containing `import Challenge` (resp.
`import Solution`), `set_option pp.explicit true`, and `#print` of the nine definitions and
`#check @` of the ten theorems, and diff the two outputs. The registry performs the same
comparison mechanically from `comparator.json`, which also names the permitted axioms and enables
an independent kernel replay; this repository carries no continuous-integration configuration.

## Data

```sh
python3 scripts/check_blocks.py
```

A standalone script (Python ≥ 3.9, standard library only) that re-derives, from the numbers alone
and reading nothing from the Lean sources:

* every block of both pools is a ranked support — distinct vertices below the modulus, the vertex
  `0` present, every rank below the stated height, and a strict rank drop along every arc — with
  the set of nonzero k-th-power residues recomputed as the full image of `z ↦ z^k mod m` over
  `z < m` with `0` removed, exactly as in the formal definition;
* every modulus is prime, hence square-free, and the moduli of a pool are pairwise coprime;
* the two exponents to twelve decimal places, and the two Ruzsa transfer values they are compared
  against;
* every rational bound carried by `RK/Numeric.lean`, each re-checked as the exact natural-power
  comparison the Lean file discharges by `decide`, and the rational assembly redone in exact
  arithmetic and compared against the decimal target and the transfer value;
* controls that must fail: a block with one rank raised to equal its predecessor's, and a block
  with one vertex moved. A checker that accepted these would be vacuous.

At this snapshot it reports `218 checks, 0 failed` and exits `0`.

## Not checked here

* **Maximality of the supports.** That no larger ranked support exists at any of the seventeen
  moduli is a search result, not a theorem, and is not verified in Lean or in the script. The
  blocks are lower-bound witnesses only.
* **Minimality of the heights.** The stored `H` is the number of rank values the block uses and is
  verified as an upper bound on the ranks; that no smaller height admits the same support is not
  claimed or checked.
* **Optimality of the pools.** Nothing establishes that these moduli, or this number of blocks,
  maximise `alpha` over the available search space.
* **The two six-element residue sets of `README.md`.** `{0, 2, 5, 7, 10, 12}` mod `17` and
  `{0, 2, 4, 6, 8, 10}` mod `13` support the transfer values the Lean theorems are compared
  against; the sets themselves, and their maximality, are exhibited and checked outside Lean —
  the Lean statements mention only the real numbers `(3 + log 6/log 17)/4` and
  `(5 + log 6/log 13)/6`.
* **The theta ceiling** quoted in `README.md` as context. It is a numerical computation, not a
  theorem of this repository, and Mathlib has no Lovász theta function.
* **The prior-art statements** in `README.md` record searches on a stated date. They are not
  mechanically verifiable, and one venue — GitHub code search outside Mathlib4 — was incomplete;
  `README.md` says so.
