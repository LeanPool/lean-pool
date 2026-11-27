/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceConjugateRoots
public import LeanPool.VacuumBellSeparation.FreeField.SourceTomita

/-!
# The physical Tomita operator in the constructed source polar coordinates

The antiunitary C₀=U C U* is an actual isometric involution. On its full
source-range domain the physical Tomita operator is exactly U C L U*,
where L is the proved positive selfadjoint ratio sqrt(Gbar)/sqrt(G).
This is a domain-sensitive factorization; modular fractional powers are
not inferred merely from it.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian.HilbertComplexification
open scoped InnerProductSpace ComplexConjugate

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable (hU : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty)

/-- Actual conjugation transported by the constructed physical polar unitary. -/
noncomputable def physicalSourceConjugation :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ⋆[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  (sourcePolarUnitary hm U hU hopen hne).symm.trans
    (conjugation.trans (sourcePolarUnitary hm U hU hopen hne))

@[simp] theorem physicalSourceConjugation_apply_polar (z : ComplexSourceHilbert hm U) :
    physicalSourceConjugation hm U hU hopen hne
      (sourcePolarUnitary hm U hU hopen hne z) =
        sourcePolarUnitary hm U hU hopen hne (conjugation z) := by
  simp only [physicalSourceConjugation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem physicalSourceConjugation_involutive (x : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalSourceConjugation hm U hU hopen hne
      (physicalSourceConjugation hm U hU hopen hne x) = x := by
  simp only [physicalSourceConjugation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, conjugation_conjugation,
    LinearIsometryEquiv.apply_symm_apply]

theorem physicalSourceConjugation_inner (x y : Lp ℂ 2 (oneParticleMeasure m)) :
    inner ℂ (physicalSourceConjugation hm U hU hopen hne x)
      (physicalSourceConjugation hm U hU hopen hne y) = conj (inner ℂ x y) := by
  simp only [physicalSourceConjugation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.inner_map_map, sourceConjugation_inner]

/-- Exact action on every point of the actual domain range κ. -/
theorem sourceTomita_polar_action (z : ComplexSourceHilbert hm U) :
    sourceTomita hm U hU (sourceRangeEquiv hm U hU z) =
      sourcePolarUnitary hm U hU hopen hne
        (conjugation (conjugateSourceGramRoot hm U z)) := by
  rw [sourceTomita_source, ← sourcePolarUnitary_sqrt_gram hm U hU hopen hne]
  change sourcePolarUnitary hm U hU hopen hne (sourceGramRoot hm U (conjugation z)) = _
  rw [sourceGramRoot_conjugation]

/-- Multiplication by C₀ makes the physical Tomita action linear. -/
theorem physicalSourceConjugation_sourceTomita (z : ComplexSourceHilbert hm U) :
    physicalSourceConjugation hm U hU hopen hne
      (sourceTomita hm U hU (sourceRangeEquiv hm U hU z)) =
        sourcePolarUnitary hm U hU hopen hne (conjugateSourceGramRoot hm U z) := by
  rw [sourceTomita_polar_action hm U hU hopen hne,
    physicalSourceConjugation_apply_polar, conjugation_conjugation]

/-- The domain equality includes both directions, before using the unbounded ratio. -/
theorem sourceTomita_domain_polar :
    ((sourceTomita hm U hU).domain : Set (Lp ℂ 2 (oneParticleMeasure m))) =
      sourcePolarUnitary hm U hU hopen hne ''
        ((sourceModularRoot hm U hU).domain : Set (ComplexSourceHilbert hm U)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨sourceGramRoot hm U z, ⟨z, rfl⟩,
      sourcePolarUnitary_sqrt_gram hm U hU hopen hne z⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    change sourcePolarUnitary hm U hU hopen hne (sourceGramRoot hm U z) ∈
      (sourceTomita hm U hU).domain
    rw [show sourcePolarUnitary hm U hU hopen hne (sourceGramRoot hm U z) =
      complexSourceMap hm U z from sourcePolarUnitary_sqrt_gram hm U hU hopen hne z]
    exact ⟨z, rfl⟩

end VacuumBellSeparation
