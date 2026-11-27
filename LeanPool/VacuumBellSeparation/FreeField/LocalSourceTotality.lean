/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.RealLinearCoherentTotality
public import LeanPool.VacuumBellSeparation.FreeField.StandardSourceSpace

/-!
# Full Fock totality of actual localized compact source pairs

The labels are the original compact real time-zero pairs with both supports
inside U. Standardness and the completed range/closure equality are proved
physical facts, not hypotheses about an auxiliary representation.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open MeasureTheory
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable (hbounded : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty)

include hbounded hopen hne

theorem sourceFock_eq_zero_of_coherent_orthogonal
    (x : SymmetricFockSpace (Lp ℂ 2 (oneParticleMeasure m)))
    (hx : ∀ u : SourceTestSpace hm U,
      inner ℂ x (coherentVector _ (timeZeroL2 hm u.1)) = 0) : x = 0 := by
  apply fock_eq_zero_of_realLinear_coherent_orthogonal (sourceTestMap hm U)
    (physicalSourceStandardSubspace hm U hbounded hopen hne) ?_ x hx
  intro v
  exact (range_sourceEmbedding_eq_closure hm U).le v.property

theorem source_coherentVector_dense_span :
    (Submodule.span ℂ (Set.range fun u : SourceTestSpace hm U =>
      coherentVector (Lp ℂ 2 (oneParticleMeasure m))
        (timeZeroL2 hm u.1))).topologicalClosure = ⊤ := by
  apply realLinear_coherentVector_dense_span (sourceTestMap hm U)
    (physicalSourceStandardSubspace hm U hbounded hopen hne)
  intro v
  exact (range_sourceEmbedding_eq_closure hm U).le v.property

end VacuumBellSeparation.Fock
