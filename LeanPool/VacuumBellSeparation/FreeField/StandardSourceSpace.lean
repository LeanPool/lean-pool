/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LocalComplexDensity
public import LeanPool.VacuumBellSeparation.FreeField.SourceGramStrictness

/-!
# The actual local one-particle source space is standard

For every bounded region with nonempty interior, complex injectivity gives
separation and the positive-energy argument gives cyclicity of its closed real
one-particle subspace. This packages precisely Mathlib's StandardSubspace.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ClosedSubmodule Set

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourceRealSpace_inf_mulI_eq_bot (hU : Bornology.IsBounded U) :
    sourceRealSpace hm U ⊓ (sourceRealSpace hm U).mulI = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply sourceRealSpace_separating hm U hU x hx.1
  have h := (ClosedSubmodule.mem_mapEquiv_iff
    (scalarSMulCLE _ Complex.UnitI) (sourceRealSpace hm U) x).mp hx.2
  have hn := (sourceRealSpace hm U).neg_mem h
  simpa [scalarSMulCLE_symm_apply, Units.smul_def, Complex.UnitI, Complex.inv_I,
    neg_smul] using hn

theorem sourceRealSpace_sup_mulI_eq_top
    (hd : DenseRange (complexSourceMap hm U)) :
    sourceRealSpace hm U ⊔ (sourceRealSpace hm U).mulI = ⊤ := by
  let S := sourceRealSpace hm U
  let T : ClosedSubmodule ℝ (Lp ℂ 2 (oneParticleMeasure m)) := S ⊔ S.mulI
  have hsub : Set.range (complexSourceMap hm U) ⊆ (T : Set _) := by
    rintro _ ⟨z, rfl⟩
    change sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im ∈ T
    apply T.add_mem
    · exact (show S ≤ T from le_sup_left)
        (show sourceEmbedding hm U z.re ∈ S from ⟨z.re, rfl⟩)
    · apply ClosedSubmodule.mem_sup.mpr
      apply subset_closure
      apply Submodule.mem_sup_right
      exact ⟨sourceEmbedding hm U z.im, ⟨z.im, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  apply closure_minimal hsub T.isClosed
  rw [hd.closure_range]
  trivial

/-- The underlying real closed subspace remains the actual physical source range. -/
noncomputable def physicalSourceStandardSubspace
    (hU : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty) :
    StandardSubspace (Lp ℂ 2 (oneParticleMeasure m)) where
  toClosedSubmodule := sourceRealSpace hm U
  IsSeparating := sourceRealSpace_inf_mulI_eq_bot hm U hU
  IsCyclic := sourceRealSpace_sup_mulI_eq_top hm U
    (complexSourceMap_denseRange_of_open hm U hopen hne)

@[simp] theorem physicalSourceStandardSubspace_toClosedSubmodule
    (hU : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty) :
    (physicalSourceStandardSubspace hm U hU hopen hne).toClosedSubmodule = sourceRealSpace hm U
      := rfl

end VacuumBellSeparation
