/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Edges
public import LeanPool.VacuumBellSeparation.FreeField.Corollary

/-!
# Theorem 1.1 and Corollary 1.2 from the estimates of Section 8

With locality of the free field proved (`locality`,
`FreeField/Microcausality/`) and Lemma 2.1 proved (`lemma_2_1`), the conditional reduction of the
main theorem (`theorem_1_1_of_section8`, the manuscript's Section 8.4) and of Corollary 1.2
(`corollary_1_2_of_theorem_1_1`) depend on a single hypothesis, `Section8Estimates`: the
estimates (8.11) and (8.13) for the double-cone algebras, uniformly in the mass.

The declarations in this module are conditional reductions.
`Section8EstimatesProof` constructs the estimates from the physical regional bounds,
and `MainTheorems` applies these reductions to that witness.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- **Theorem 1.1 from the estimates of Section 8**: `Section8Estimates` implies Theorem 1.1
(locality and Lemma 2.1 are proved). -/
theorem theorem_1_1_of_section8Estimates (h8 : Section8Estimates) : Theorem_1_1 :=
  theorem_1_1_of_section8 h8 locality

/-- **Corollary 1.2 from the estimates of Section 8**: `Section8Estimates` implies Corollary 1.2. -/
theorem corollary_1_2_of_section8Estimates (h8 : Section8Estimates) : Corollary_1_2 :=
  corollary_1_2_of_theorem_1_1 (theorem_1_1_of_section8Estimates h8)

end VacuumBellSeparation
