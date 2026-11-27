/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CutoffFourierKernel
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Uniform continuity in the parameter of compactly supported kernels

Joint continuity and a common compact support imply continuity in the actual
supremum norm. We apply this to all weighted derivatives of the cutoff Fourier
kernel. Pointwise continuity alone is not used as a substitute for this norm
continuity.
-/

@[expose] public section

open Filter Set
open scoped BoundedContinuousFunction Topology SchwartzMap FourierTransform InnerProductSpace

namespace VacuumBellSeparation

theorem continuous_boundedContinuousFunction_of_common_compact_support
    {P X F : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [NormedAddCommGroup F] (f : P → X →ᵇ F)
    {K : Set X} (hK : IsCompact K)
    (hf : Continuous (fun z : P × X => f z.1 z.2))
    (hz : ∀ p x, x ∉ K → f p x = 0) : Continuous f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : P → C(K, F) := fun p =>
    ⟨fun x => f p x, (f p).continuous.comp continuous_subtype_val⟩
  have hfK : Continuous fK := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [ContinuousAt, BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  have h := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hfK.tendsto p)
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with q hq x
  by_cases hx : x ∈ K
  · exact hq ⟨x, hx⟩
  · simp only [hz p x hx, hz q x hx, dist_self]
    exact hε

/-- Partial iterated derivatives of a jointly smooth function vary continuously
in both the parameter and the differentiated variable. -/
theorem continuous_partial_iteratedFDeriv
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) :
    Continuous (fun z : P × E => iteratedFDeriv ℝ j (fun y => f (z.1, y)) z.2) := by
  let a : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  let A := ContinuousMultilinearMap.compContinuousLinearMapL (F := F) (fun _ : Fin j => a)
  have heq (p : P) (x : E) :
      iteratedFDeriv ℝ j (fun y => f (p, y)) x = A (iteratedFDeriv ℝ j f (p, x)) := by
    have ht : ContDiff ℝ (⊤ : ℕ∞) (fun z : P × E => f ((p, 0) + z)) :=
      hf.comp (contDiff_const.add contDiff_id)
    have h := a.iteratedFDeriv_comp_right ht x (i := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    simpa only [A, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      Function.comp_def, iteratedFDeriv_comp_add_left, a,
      ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using h
  have h := A.continuous.comp (hf.continuous_iteratedFDeriv (m := j) (mod_cast le_top))
  exact h.congr (fun z => (heq z.1 z.2).symm)

theorem continuous_cutoffFourierKernel_weightedDerivative
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (k j : ℕ) :
    Continuous (fun p => schwartzWeightedDerivative k j (cutoffFourierKernel χ p)) := by
  apply continuous_boundedContinuousFunction_of_common_compact_support _ hχ
  · have hf : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          spatialFourierCharacter z.1 z.2 * χ z.2) := by
      simp only [spatialFourierCharacter, Real.fourierChar_apply]
      exact (Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
          ((contDiff_fst.inner ℝ contDiff_snd).neg))).mul contDiff_const)).mul
        ((χ.smooth ⊤).comp contDiff_snd)
    have h := continuous_partial_iteratedFDeriv hf j
    have heq (p : EuclideanSpace ℝ (Fin 3)) :
        (fun x => spatialFourierCharacter p x * χ x) = cutoffFourierKernel χ p := by
      funext x
      exact (cutoffFourierKernel_apply χ p x).symm
    simp_rw [heq] at h
    exact ((continuous_norm.comp continuous_snd).pow k).smul h
  · intro p x hx
    have hd : iteratedFDeriv ℝ j (cutoffFourierKernel χ p) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h =>
        hx ((tsupport_cutoffFourierKernel_subset χ p) ((tsupport_iteratedFDeriv_subset j) h))
    simp only [schwartzWeightedDerivative_apply, hd, smul_zero]

/-- Continuity holds in the finite Banach product used by the actual distribution factorization. -/
theorem continuous_schwartzDerivativeMap_cutoffFourierKernel
    (s : Finset (ℕ × ℕ))
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    Continuous (fun p => schwartzDerivativeMap s (cutoffFourierKernel χ p)) := by
  apply continuous_pi
  intro i
  exact continuous_cutoffFourierKernel_weightedDerivative χ hχ i.val.1 i.val.2

end VacuumBellSeparation
