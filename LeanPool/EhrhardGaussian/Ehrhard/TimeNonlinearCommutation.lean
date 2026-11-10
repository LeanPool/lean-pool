/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimeOUComposition
public import LeanPool.EhrhardGaussian.Ehrhard.OUNonlinearCommutation

/-! # Nonlinear OU commutation with a time-dependent outer functional -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- The time derivative adds the partial time derivative of the outer
functional to the negative Hessian contraction. Compact time slabs discharge
the integral differentiation hypotheses. -/
theorem hasDerivAt_time_ou_nonlinear_commutation_local {n k : ℕ}
    {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i))
    {a b G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc a b)
    (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (f i) j) l y| ≤ H)
    {J : ℝ × (Fin k → ℝ) → ℝ}
    {l u t T : ℝ} (hl : 0 < l) (hlt : l < t) (htu : t < u) (huT : u ≤ T)
    (hJ : ∀ s ∈ Icc l u, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 J (s, z))
    (x : Fin n → ℝ) :
    HasDerivAt (ouSpaceTimeAverage (J ∘ ouSpaceTimeFamily f) T x)
      (ouAverage (fun y => fderiv ℝ J (t, ouFamily f (t, y)) (1, 0) -
        ouHessianContraction (fun z => J (t, z)) f t y) x (T - t)) t := by
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hf i)
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf₂ i)
  let F := J ∘ ouSpaceTimeFamily f
  let Ψ := fun z => J (t, z)
  let g := fun y => ouFamily f (t, y)
  have ht : 0 < t := hl.trans hlt
  have hF : ContDiffOn ℝ 1 F (Ioo l u ×ˢ univ) :=
    contDiffOn_time_ouComposition hf₁ hl hbound hJ
  have hΨ (z) (hz : ∀ i, z i ∈ Icc a b) : ContDiffAt ℝ 2 Ψ z :=
    (hJ t ⟨hlt.le, htu.le⟩ z hz).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hrange (y) := ouFamily_mem_Icc hf₁ hbound y t
  have hΨg (y) := hΨ _ (hrange y)
  have hg : ContDiff ℝ 2 g := contDiff_ouFamily_space hf t
  have hsection := hasPolynomiallyBoundedSecond_ouComposition hf hG hH hbound hgrad hsecond hΨ ht.le
  obtain ⟨C, hC, hdom⟩ := exists_time_ouComposition_bound hf₂ hl hG hH hbound hgrad
    (fun i j y => hsecond i j j y) hJ
  have h := hasDerivAt_ouSpaceTimeAverage_generator isOpen_Ioo ⟨hlt, htu⟩
    (fun _ hs => hs.2.trans_le huT) hF hsection hC (N := 1)
    (fun s hs y => by
      simpa only [F, ouSpaceTimeFamily, Function.comp_def, pow_one] using hdom s hs y) x
  have htime (y : Fin n → ℝ) : fderiv ℝ F (t, y) (1, 0) =
      fderiv ℝ J (t, g y) (1, 0) +
        ∑ i, coordinateDerivative Ψ i (g y) * ouGenerator (fun z => g z i) y := by
    have hp : (t, y) ∈ Ioo l u ×ˢ (univ : Set (Fin n → ℝ)) := ⟨⟨hlt, htu⟩, mem_univ _⟩
    have hdiff := (hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt_one
    have houter := (hJ t ⟨hlt.le, htu.le⟩ _ (hrange y)).differentiableAt (by norm_num : (2 : WithTop
      ℕ∞) ≠ 0)
    have hder := houter.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id' t).prodMk (hasDerivAt_ouFamily hf₂ y ht))
    rw [← deriv_spaceTime_left hdiff]
    change deriv (J ∘ fun s => (s, ouFamily f (s, y))) t = _
    rw [hder.deriv, fderiv_spaceTime_split houter, concentration_fderiv_apply_eq_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hcancel : (fun y => fderiv ℝ F (t, y) (1, 0) - ouGenerator (fun z => F (t, z)) y) =
      fun y => fderiv ℝ J (t, ouFamily f (t, y)) (1, 0) - ouHessianContraction Ψ f t y := by
    funext y
    rw [htime]
    have hgen := ouGenerator_comp hΨg hg y
    change ouGenerator (fun z => F (t, z)) y = _ at hgen
    rw [hgen]
    dsimp only [ouHessianContraction, g, ouFamily]
    ring
  rw [hcancel] at h
  exact h


end EhrhardGaussian.Ehrhard

end
