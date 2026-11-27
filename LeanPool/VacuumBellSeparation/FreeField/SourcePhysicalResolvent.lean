/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceTomita
public import LeanPool.VacuumBellSeparation.FreeField.SourceConjugateRoots
public import LeanPool.VacuumBellSeparation.FreeField.AntilinearGraphAdjoint

/-!
# A resolvent vector in the full original source Tomita square

The literal source map κ and its actual Hilbert adjoint give R=κκ*/2.
For every physical vector ψ, (Rψ,ψ-Rψ) belongs to the universal S*S
relation of the full original source graph. No bounded-region, inverse,
core or modular-identification premise enters this statement.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap Gaussian Gaussian.HilbertComplexification
open scoped InnerProductSpace ComplexConjugate

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Continuous linear map for the source physical resolvent, of type `Lp ℂ 2 (oneParticleMeasure m)
→L[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def sourcePhysicalResolvent :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  (1 / 2 : ℝ) • (complexSourceMap hm U).comp (complexSourceMap hm U).adjoint

theorem sourceGram_conjugation (z : ComplexSourceHilbert hm U) :
    sourceGram hm U (conjugation z) = conjugation (conjugateSourceGram hm U z) := by
  simp only [conjugateSourceGram, conjugateOperator_apply, conjugation_conjugation]

theorem sourceConjugatePair_inner (v w : ComplexSourceHilbert hm U) :
    inner ℂ (complexSourceMap hm U (conjugation v))
      (complexSourceMap hm U (conjugation w)) =
        inner ℂ (conjugateSourceGram hm U w) v := by
  rw [← (complexSourceMap hm U).adjoint_inner_right]
  change inner ℂ (conjugation v) (sourceGram hm U (conjugation w)) = _
  rw [sourceGram_conjugation, sourceConjugation_inner, inner_conj_symm]

theorem sourcePhysicalResolvent_mem_square (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (sourcePhysicalResolvent hm U ψ, ψ - sourcePhysicalResolvent hm U ψ) ∈
      antilinearGraphSquare (sourceTomitaGraph hm U) := by
  let w : ComplexSourceHilbert hm U := (1 / 2 : ℝ) • (complexSourceMap hm U).adjoint ψ
  have hw : complexSourceMap hm U w = sourcePhysicalResolvent hm U ψ := by
    simp only [w, sourcePhysicalResolvent, map_smul_of_tower, smul_apply, comp_apply]
  have htwo : (2 : ℝ) • w = (complexSourceMap hm U).adjoint ψ := by
    simp only [w, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  have hH : conjugateSourceGram hm U w =
      (complexSourceMap hm U).adjoint (ψ - complexSourceMap hm U w) := by
    rw [conjugateSourceGram_eq_two_sub]
    simp only [sub_apply, ofNat_apply, map_sub]
    change (2 : ℕ) • w - sourceGram hm U w =
      (complexSourceMap hm U).adjoint ψ - sourceGram hm U w
    rw [show (2 : ℕ) • w = (2 : ℝ) • w by simp only [two_smul], htwo]
  refine ⟨complexSourceMap hm U (conjugation w), ⟨w, hw, rfl⟩, ?_⟩
  rintro x y ⟨v, rfl, rfl⟩
  change inner ℂ (complexSourceMap hm U (conjugation v))
    (complexSourceMap hm U (conjugation w)) =
      inner ℂ (ψ - sourcePhysicalResolvent hm U ψ) (complexSourceMap hm U v)
  rw [sourceConjugatePair_inner, hH, (complexSourceMap hm U).adjoint_inner_left, hw]

end VacuumBellSeparation
