# Authorship and automation

JD Jones directed this project, chose its objective, and is its human author and responsible
maintainer. He is not a party to the mathematics: the directed method with a ranking is Dmitry
Krachun's, at `k = 2`; the residue transfer it is compared against is Imre Ruzsa's; the blocks of
the two pools were found by computer search; and the Lean development was written by AI agents
under his direction. No independent human mathematical review is recorded.

## What the AI did

Anthropic's Claude models did the work, run through Claude Code:

* Claude Fable 5.1 planned the formalization — the general-`k` statements of `Challenge.lean`, the
  module architecture, the decision to carry the digit stride `k` as a parameter of every lemma,
  the shape of the numeric layer — reviewed the subagents' output, and assembled the result.
* Claude Opus subagents, several in parallel, wrote the Lean modules (the digit toolkit and the
  composite lift; the word argument and the passage to integers; the Chinese-remainder glue and
  the stage construction; the allocation, the limit and the passage to all `N`; the finite block
  verifications and the exponent inequalities), searched the literature and the formalization
  registries for the prior-art statement in `README.md`, wrote this documentation, and audited the
  result for statement fidelity, axioms and documentation accuracy.
* Claude Opus subagents also found the blocks. The search ran on one desktop machine on
  2026-09-12 and used four methods: a CP-SAT model, per candidate modulus, for a maximum vertex
  set admitting a ranking of a given height; tabu search to extend the sizes the model could not
  close; an exact branch-and-bound that quotients the search by the multiplier symmetry of the
  k-th-power residues, which is what settles the smaller moduli exhaustively; and, for the block
  at `51 = 3 · 17`, the interval construction described in `README.md`, which needs no search at
  all beyond computing `max Q_4(51)` and checking that no longer interval works. **No solver is
  in the trust chain.** Every block that survives into the repository is re-verified twice
  independently of the search — in Lean by `decide`, in the kernel, from the definition of a
  nonzero k-th-power residue; and in `scripts/check_blocks.py` by a standard-library recomputation
  that reads nothing from the Lean sources and carries controls that must fail.

The Lean kernel checked every proof. `Test/Axioms.lean` audits the axioms of every declaration of
the development; no `native_decide`, no custom axiom, and no `sorry` occurs in `RK/`,
`Solution.lean` or `Test/`. Prompt, token and monetary accounting was not retained.

## Sources and credit

The ranked-block construction is Krachun's (arXiv:2608.01325), for squares. Reading the same
object as an acyclic digraph under "the difference is a nonzero k-th-power residue", carried with a
topological ranking, and running the lift, the glue and the allocation at a general exponent `k`,
is this repository's reformulation, and is not attributed to him. The digit method underneath
descends from Ruzsa (doi:10.1007/BF02454169), whose Theorem 2 already covers every `k`; Younis
restates that transfer in the form used here (arXiv:1908.06058, Theorem 1.4); the search pattern
for k-th-power-difference-free residue sets follows Lewko (doi:10.37236/4656) and
Beigel–Gasarch (arXiv:0804.4892). All are cited in `README.md`, `PROOF.md` and
`formalization.yaml`.

The contribution of this repository is: the formal statement and proof of the directed
construction at every `k ≥ 2`; the two pools as new data, including the observation that an
interval of `t ≤ m − max Q` consecutive residues is a block at any square-free modulus, prime or
not, which is where `pool4`'s block at `51 = 3 · 17` comes from; and the two exponent
inequalities, proved by exact comparisons of natural powers rather than numerically.

## Limits

* The theorems are lower bounds. Nothing is claimed about upper bounds, and the known upper bounds
  for `D_k(N)` are all of the form `N^{1−o(1)}`, so the gap remains wide at every `k`.
* Maximality of the supports, minimality of the heights and optimality of the pools are search
  results at best, and are not theorems here — even at the moduli where the search was exhaustive
  and the size is therefore known to be exact. See the "Not checked here" section of
  `VERIFICATION.md`.
* The theta ceiling discussed in `README.md` is cited context and a numerical computation. It is
  explicitly outside the formal development: Mathlib has no Lovász theta function, and no theorem
  of this repository mentions it.
* The prior-art statements in `README.md` record what was searched on the stated date; they are
  not a guarantee that nothing else exists, and one venue (GitHub code search outside Mathlib4)
  was incomplete.
* Registration at a formalization registry certifies statement matching and kernel replay at one
  commit. It does not certify novelty or significance.
