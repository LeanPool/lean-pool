/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineDescription
public import LeanPool.KLRandomness.StageEstimates

/-!
# Separation reduction with the concrete affine interpreter

The remaining hypotheses concern the actual blocks, their stage estimates,
and sufficiently short binary programs describing events that cover their
solutions. Uniform enumerability and the Martin-Löf measure bounds are
discharged by the implemented interpreter and verifier.

These are conditional separation theorems. The separate `StageConstruction`
development supplies their actual stage sequence and short-program bounds;
`Separation` obtains the resulting unconditional existence theorem.
-/

@[expose] public section

namespace Klr

/-- Actual stage estimates and short, successfully evaluated affine programs imply separation.
The program may describe any verified affine event containing the selected block event. -/
theorem exists_separating_of_stage_estimates_and_affine_programs (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (V : ℕ → ℕ)
    (hstage : ∀ s : BettingStrategy, ∃ (H : Set Cantor) (J : ℕ),
      StageEstimates B s.normalize.scan s.normalize.capital.wager V H J)
    (hprogram : ∀ n : ℕ, ∃ (j : ℕ) (p : List Bool) (c : AffineCode.Data),
      c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
      2 * p.length + n + 1 ≤ AffineCode.rank c ∧ (B j).event ⊆ AffineCode.event c) :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  apply exists_separating_of_stage_estimates_and_descriptions B hdis V hstage
    AffineDescription.rePred_W AffineDescription.per_program_bound
  intro n
  obtain ⟨j, p, c, hc, hv, hr, hcover⟩ := hprogram n
  exact ⟨j, p, by rwa [AffineDescription.cylinderUnion_W_eq hc hv hr]⟩

/-- Describing the selected block's exact event is a sufficient special case of the cover. -/
theorem exists_separating_of_stage_estimates_and_exact_affine_programs (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (V : ℕ → ℕ)
    (hstage : ∀ s : BettingStrategy, ∃ (H : Set Cantor) (J : ℕ),
      StageEstimates B s.normalize.scan s.normalize.capital.wager V H J)
    (hprogram : ∀ n : ℕ, ∃ (j : ℕ) (p : List Bool) (c : AffineCode.Data),
      c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
      2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = (B j).event) :
    ∃ X : Cantor, KolmogorovLovelandRandom X ∧ ¬MartinLofRandom X := by
  apply exists_separating_of_stage_estimates_and_affine_programs B hdis V hstage
  intro n
  obtain ⟨j, p, c, hc, hv, hr, he⟩ := hprogram n
  exact ⟨j, p, c, hc, hv, hr, he.symm.subset⟩

end Klr
