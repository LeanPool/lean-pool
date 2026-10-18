/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/

module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanMain
public import LeanPool.CongruenceNormalizers.NormalizerDelta.NewmanDelta

/-!
# Newman normalizer bounds for congruence subgroups

Source: doi:10.1017/S001708950000940X, url:https://github.com/F-Najman/normalizer-lean/tree/ea4445c0d991a65d54fc77af0af559f2322e8660
Authors: Filip Najman
Status: verified
Main declarations: `CongruenceNormalizers.newman_iff`, `CongruenceNormalizers.newman_delta`
Tags: modular-forms, congruence-subgroups, normalizers, arithmetic-groups
MSC: 11F06, 20H05
-/

/-
Adapted from Filip Najman's Apache-2.0 `normalizer-lean`, commit
`ea4445c0d991a65d54fc77af0af559f2322e8660`. The upstream proofs were written by
Claude Code agents following the author's mathematical blueprints.
-/

public section

namespace CongruenceNormalizers

open Matrix MatrixGroups

/-- Newman's integral matrix form characterizes the real normalizer of Γ₀(N). -/
theorem newman_iff {N : ℕ} [NeZero N] {g : SL(2, ℝ)} :
    g ∈ Norm0 N ↔ IsNewmanForm N g :=
  ⟨newman', newmanForm_mem_normalizer'⟩

/-- The corresponding necessary matrix form for the normalizer of Γ_Δ(N). -/
theorem newman_delta {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    {g : SL(2, ℝ)} (hg : g ∈ NormG (GammaDeltaR N Δ)) :
    IsNewmanFormH N (hDelta N Δ) g :=
  newman_delta' Δ hg

end CongruenceNormalizers
