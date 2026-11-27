/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompletedComplexInjectivity
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexConjugation

/-!
# Strict source Gram forms and the separating real subspace

Injectivity of the actual completed complex source map gives a strictly
positive quadratic form and injective Gram operators, without asserting a
uniform spectral gap or bounded inverse. The closed real source space is
separating. Cyclicity/dense range, and hence full standardness, are proved in other modules
for bounded open nonempty regions (`complexSourceMap_denseRange_of_open` in
`FreeField/LocalComplexDensity.lean`; `sourceRealSpace_sup_mulI_eq_top` and
`physicalSourceStandardSubspace` in `FreeField/StandardSourceSpace.lean`).
-/

@[expose] public section

open MeasureTheory
open VacuumBellSeparation.Gaussian.HilbertComplexification
open scoped InnerProductSpace

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourceGram_isPositive : (sourceGram hm U).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (complexSourceMap hm U)

theorem inner_sourceGram_re_eq_norm_sq (z : ComplexSourceHilbert hm U) :
    (inner ℂ z (sourceGram hm U z)).re = ‖complexSourceMap hm U z‖ ^ 2 :=
  ((complexSourceMap hm U).apply_norm_sq_eq_inner_adjoint_right z).symm

theorem inner_sourceGram_pos (hU : Bornology.IsBounded U)
    (z : ComplexSourceHilbert hm U) (hz : z ≠ 0) :
    0 < (inner ℂ z (sourceGram hm U z)).re := by
  rw [inner_sourceGram_re_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h =>
    hz (complexSource_eq_zero_of_map_eq_zero hm U hU z h)))

theorem sourceGram_injective (hU : Bornology.IsBounded U) :
    Function.Injective (sourceGram hm U) := by
  intro z w h
  apply sub_eq_zero.mp
  have hg : sourceGram hm U (z - w) = 0 := by rw [map_sub, h, sub_self]
  by_contra hz
  have hp := inner_sourceGram_pos hm U hU (z - w) hz
  simp only [hg, inner_zero_right, Complex.zero_re, lt_self_iff_false] at hp

theorem conjugateSourceGram_injective (hU : Bornology.IsBounded U) :
    Function.Injective (Gaussian.conjugateOperator (sourceGram hm U)) := by
  intro z w h
  apply (conjugation (E := SourceHilbert hm U)).injective
  apply sourceGram_injective hm U hU
  exact (conjugation (E := SourceHilbert hm U)).injective h

/-- The actual real range has trivial intersection with its imaginary multiple. -/
theorem sourceRealSpace_separating (hU : Bornology.IsBounded U)
    (x : Lp ℂ 2 (oneParticleMeasure m))
    (hx : x ∈ sourceRealSpace hm U) (hix : Complex.I • x ∈ sourceRealSpace hm U) : x = 0 := by
  change ∃ u, sourceEmbedding hm U u = x at hx
  change ∃ v, sourceEmbedding hm U v = Complex.I • x at hix
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hix
  let z : ComplexSourceHilbert hm U := Gaussian.HilbertComplexification.mk v (-u)
  have hz : complexSourceMap hm U z = 0 := by
    change sourceEmbedding hm U v + Complex.I • sourceEmbedding hm U (-u) = 0
    rw [map_neg, hu, hv, smul_neg, add_neg_cancel]
  have hz0 := complexSource_eq_zero_of_map_eq_zero hm U hU z hz
  have hu0 : u = 0 := by
    have h := congrArg (fun w : ComplexSourceHilbert hm U => w.im) hz0
    simpa [z] using h
  rw [hu0, map_zero] at hu
  exact hu.symm

end VacuumBellSeparation
