/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Explicit

/-!
# Read's theorem on ℓ¹, in the form of Formal Conjectures

`InvariantSubspaceProblem.Invariant_subspace_problem_l1` asks for a bounded operator on
`lp (fun _ : ℕ => ℂ) 1` with no nontrivial closed invariant subspace. Śliwa's version of Read's
operator (`ReadL1.readOp`), built from the explicit sequence `ReadL1.dRead`, is one
(`ReadL1.theorem7`, `ReadL1.theorem7Hyp_dRead`).
-/

@[expose] public section

namespace ReadL1

open InvariantSubspaceProblem

/-- **Read's theorem on ℓ¹** (Read 1985; Śliwa 2010): there is a bounded operator on ℓ¹ with no
nontrivial closed invariant subspace. The statement is Formal Conjectures'
`Invariant_subspace_problem_l1`, verbatim. -/
theorem invariant_subspace_problem_l1 :
    ∃ (T : (lp (fun (_ : ℕ) => ℂ) 1) →L[ℂ] (lp (fun (_ : ℕ) => ℂ) 1)),
    IsEmpty (ClosedInvariantSubspace T) :=
  ⟨readOp theorem7Hyp_dRead.toGrowthHyp, theorem7 theorem7Hyp_dRead⟩

end ReadL1
