/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.StandardSourceSpace
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticAlgebra

/-!
# Standardness from an actual open spatial complement

Completed source vectors in disjoint regions have zero imaginary pairing.
The complex density of any nonempty open complementary region then makes
the original real source space separating. This applies to unbounded
halfspaces and does not assume a wedge modular identification.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ClosedSubmodule
open scoped InnerProductSpace ComplexConjugate

variable {m : ℝ} (hm : 0 < m)
  {U W : Set (EuclideanSpace ℝ (Fin 3))} (hUW : Disjoint U W)

include hUW in
theorem sourceEmbedding_cross_im_zero (u : SourceHilbert hm U) (v : SourceHilbert hm W) :
    (⟪sourceEmbedding hm U u, sourceEmbedding hm W v⟫_ℂ).im = 0 := by
  refine UniformSpace.Completion.induction_on u (isClosed_eq (by fun_prop) continuous_const) ?_
  intro u
  refine UniformSpace.Completion.induction_on v (isClosed_eq (by fun_prop) continuous_const) ?_
  intro v
  rw [sourceEmbedding_coe, sourceEmbedding_coe, inner_timeZeroL2_gram]
  simp [timeZeroSymplectic_eq_zero_of_disjoint hUW u.2 v.2]

include hUW in
theorem sourceRealSpace_cross_im_zero
    {x y : Lp ℂ 2 (oneParticleMeasure m)}
    (hx : x ∈ sourceRealSpace hm U) (hy : y ∈ sourceRealSpace hm W) :
    (⟪x, y⟫_ℂ).im = 0 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact sourceEmbedding_cross_im_zero hm hUW u v

include hUW in
theorem sourceRealSpace_separating_of_open_complement
    (hW : IsOpen W) (hne : W.Nonempty)
    (x : Lp ℂ 2 (oneParticleMeasure m))
    (hx : x ∈ sourceRealSpace hm U) (hix : Complex.I • x ∈ sourceRealSpace hm U) : x = 0 := by
  have hreal (v : SourceHilbert hm W) : ⟪x, sourceEmbedding hm W v⟫_ℂ = 0 := by
    have hi := sourceRealSpace_cross_im_zero hm hUW hx (show sourceEmbedding hm W v ∈
      sourceRealSpace hm W from ⟨v, rfl⟩)
    have hr := sourceRealSpace_cross_im_zero hm hUW hix (show sourceEmbedding hm W v ∈
      sourceRealSpace hm W from ⟨v, rfl⟩)
    rw [inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_im, Complex.I_mul_im] at hr
    exact Complex.ext (neg_eq_zero.mp hr) hi
  have hcomplex (z : ComplexSourceHilbert hm W) : ⟪x, complexSourceMap hm W z⟫_ℂ = 0 := by
    change ⟪x, sourceEmbedding hm W z.re + Complex.I • sourceEmbedding hm W z.im⟫_ℂ = 0
    rw [inner_add_right, inner_smul_right, hreal, hreal, mul_zero, add_zero]
  have hall (y : Lp ℂ 2 (oneParticleMeasure m)) : ⟪x, y⟫_ℂ = 0 :=
    (complexSourceMap_denseRange_of_open hm W hW hne).induction_on y
      (isClosed_eq (by fun_prop) continuous_const) hcomplex
  exact inner_self_eq_zero.mp (hall x)

include hUW in
theorem complexSourceMap_injective_of_open_complement
    (hW : IsOpen W) (hne : W.Nonempty) : Function.Injective (complexSourceMap hm U) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change sourceEmbedding hm U z.re + Complex.I • sourceEmbedding hm U z.im = 0 at hz
  have him : sourceEmbedding hm U z.im = 0 := by
    apply sourceRealSpace_separating_of_open_complement hm hUW hW hne _ ⟨z.im, rfl⟩
    refine ⟨-z.re, ?_⟩
    rw [map_neg]
    change -(sourceEmbedding hm U z.re) = Complex.I • sourceEmbedding hm U z.im
    apply add_left_cancel (a := sourceEmbedding hm U z.re)
    rw [add_neg_cancel, hz]
  have hre : sourceEmbedding hm U z.re = 0 := by simpa only [him, smul_zero, add_zero] using hz
  apply Gaussian.HilbertComplexification.ext
  · exact (sourceEmbedding hm U).injective (by simpa only
      [Gaussian.HilbertComplexification.re_zero, map_zero] using hre)
  · exact (sourceEmbedding hm U).injective (by simpa only
      [Gaussian.HilbertComplexification.im_zero, map_zero] using him)

include hUW in
theorem sourceRealSpace_inf_mulI_eq_bot_of_open_complement
    (hW : IsOpen W) (hne : W.Nonempty) :
    sourceRealSpace hm U ⊓ (sourceRealSpace hm U).mulI = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply sourceRealSpace_separating_of_open_complement hm hUW hW hne x hx.1
  have h := (ClosedSubmodule.mem_mapEquiv_iff
    (scalarSMulCLE _ Complex.UnitI) (sourceRealSpace hm U) x).mp hx.2
  have hn := (sourceRealSpace hm U).neg_mem h
  simpa [scalarSMulCLE_symm_apply, Units.smul_def, Complex.UnitI, Complex.inv_I, neg_smul] using hn

/-- The literal actual source standard subspace, including unbounded regions
whose spatial complement contains a nonempty open region. -/
noncomputable def physicalSourceStandardSubspaceOfComplement
    (hU : IsOpen U) (hneU : U.Nonempty) (hW : IsOpen W) (hneW : W.Nonempty) :
    StandardSubspace (Lp ℂ 2 (oneParticleMeasure m)) where
  toClosedSubmodule := sourceRealSpace hm U
  IsSeparating := sourceRealSpace_inf_mulI_eq_bot_of_open_complement hm hUW hW hneW
  IsCyclic := sourceRealSpace_sup_mulI_eq_top hm U
    (complexSourceMap_denseRange_of_open hm U hU hneU)

end VacuumBellSeparation
