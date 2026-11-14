/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalRegularity
public import LeanPool.EhrhardGaussian.Ehrhard.GeneratorChainRule
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform derivative bounds on compact subsets of the probability box -/

@[expose] public noncomputable section

open Set
open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped ContDiff

namespace EhrhardGaussian.Ehrhard

/-- A coordinate derivative of a twice continuously differentiable function is continuously
differentiable. -/
theorem contDiffAt_coordinateDerivative {k : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    {x : Fin k → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ x) (i : Fin k) :
    ContDiffAt ℝ 1 (coordinateDerivative Ψ i) x :=
  (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- Local smoothness on a compact carrier gives a common bound on all
derivatives needed for the nonlinear OU chain rule. -/
theorem IsCompact.exists_bound_secondDerivatives {k : ℕ} {K : Set (Fin k → ℝ)}
    (hK : IsCompact K) {Ψ : (Fin k → ℝ) → ℝ}
    (hΨ : ∀ z ∈ K, ContDiffAt ℝ 2 Ψ z) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z ∈ K, |Ψ z| ≤ M) ∧
      (∀ z ∈ K, ‖fderiv ℝ Ψ z‖ ≤ M) ∧
      (∀ i z, z ∈ K → |coordinateDerivative Ψ i z| ≤ M) ∧
      ∀ i j z, z ∈ K → |coordinateDerivative (coordinateDerivative Ψ i) j z| ≤ M := by
  let Q := fun z => (Ψ z, fderiv ℝ Ψ z,
    fun i : Fin k => fderiv ℝ (coordinateDerivative Ψ i) z)
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply (hΨ z hz).continuousAt.prodMk
    apply ((hΨ z hz).continuousAt_fderiv (by norm_num)).prodMk
    exact continuousAt_pi.mpr fun i =>
      (contDiffAt_coordinateDerivative (hΨ z hz) i).continuousAt_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨max C 0, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [Real.norm_eq_abs] using
      (norm_fst_le (Q z)).trans ((hC z hz).trans (le_max_left _ _))
  · intro z hz
    exact (norm_fst_le (Q z).2).trans ((norm_snd_le (Q z)).trans
      ((hC z hz).trans (le_max_left _ _)))
  · intro i z hz
    have hd : ‖fderiv ℝ Ψ z‖ ≤ max C 0 :=
      (norm_fst_le (Q z).2).trans ((norm_snd_le (Q z)).trans
        ((hC z hz).trans (le_max_left _ _)))
    simpa only [coordinateDerivative, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      ((fderiv ℝ Ψ z).le_opNorm (Pi.single i 1)).trans
        (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  · intro i j z hz
    have hd : ‖fderiv ℝ (coordinateDerivative Ψ i) z‖ ≤ max C 0 :=
      (norm_le_pi_norm (Q z).2.2 i).trans ((norm_snd_le (Q z).2).trans
        ((norm_snd_le (Q z)).trans ((hC z hz).trans (le_max_left _ _))))
    simpa only [coordinateDerivative, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      ((fderiv ℝ (coordinateDerivative Ψ i) z).le_opNorm (Pi.single j 1)).trans
        (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

/-- A closed probability subbox is compact, including the zero-coordinate case. -/
theorem isCompact_probabilitySubbox {k : ℕ} (a b : ℝ) :
    IsCompact {z : Fin k → ℝ | ∀ i, z i ∈ Icc a b} := by
  simpa only [Set.pi, mem_univ, forall_const] using
    (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc a b)))


end EhrhardGaussian.Ehrhard

end
