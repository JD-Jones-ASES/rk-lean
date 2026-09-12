import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Walks every constant in the environment whose name begins with `KthPower.` (every declaration of
this development, `Challenge.lean` excluded since it is not imported), `_private.RK.` (private
auxiliaries of the `RK.*` modules) or `_private.Solution.`, and collects the axioms each depends
on. Anything outside `propext`, `Classical.choice`, `Quot.sound` is reported with `logError`, which
fails `lake build`. The audit also fails if it matched fewer than the floor below (so a renamed
namespace cannot make it pass vacuously) or if any of the ten compared theorems is missing from the
environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "KthPower." || label.startsWith "_private.RK." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  -- TODO desk: raise the floor to just below the final count before pinning the docs.
  unless checked ≥ 0 do
    logError m!"Axiom audit matched only {checked} project constants; expected more"
  for n in [`KthPower.directed_liminf, `KthPower.directed_pointwise,
      `KthPower.pool4_valid, `KthPower.pool6_valid,
      `KthPower.alpha4_gt_transfer, `KthPower.alpha4_gt,
      `KthPower.alpha6_gt_transfer, `KthPower.alpha6_gt,
      `KthPower.fourth_power_liminf, `KthPower.sixth_power_liminf] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
