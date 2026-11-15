/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUComposition

/-!
# The nonlinear OU commutation identity

The backward generator cancels the componentwise OU evolution, leaving the
negative Hessian contraction. The Hessian is evaluated at the smoothed vector.
All differentiation and domination hypotheses are supplied by the concrete
bounded smooth inputs and the compact probability subbox.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- The carré-du-champ contraction for a finite family of smoothed inputs. -/
def ouHessianContraction {n k : ℕ} (Ψ : (Fin k → ℝ) → ℝ)
    (f : Fin k → (Fin n → ℝ) → ℝ) (t : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ l, coordinateDerivative (coordinateDerivative Ψ i) l (ouFamily f (t, y)) *
    ∑ j, coordinateDerivative (fun z => ouAverage (f i) z t) j y *
      coordinateDerivative (fun z => ouAverage (f l) z t) j y

/-- The nonlinear semigroup commutation identity holds in independent Gaussian coordinates,
including singular correlated families represented by dependent inputs. -/
theorem hasDerivAt_ou_nonlinear_commutation {n k : ℕ}
    {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i))
    {a b G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc a b)
    (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (f i) j) l y| ≤ H)
    {Ψ : (Fin k → ℝ) → ℝ}
    (hΨ : ∀ z, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 Ψ z)
    (x : Fin n → ℝ) {t T : ℝ} (ht : 0 < t) (hT : t < T) :
    HasDerivAt (ouSpaceTimeAverage (Ψ ∘ ouFamily f) T x)
      (-ouAverage (ouHessianContraction Ψ f t) x (T - t)) t := by
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hf i)
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf₂ i)
  let F := Ψ ∘ ouFamily f
  let g := fun y => ouFamily f (t, y)
  have hrange (y) := ouFamily_mem_Icc hf₁ hbound y t
  have hΨg (y) := hΨ _ (hrange y)
  have hg : ContDiff ℝ 2 g := contDiff_ouFamily_space hf t
  have hF := contDiffOn_ouComposition hf₁ hbound hΨ
  obtain ⟨C, hC, hdom⟩ := exists_ouComposition_spaceTime_bound hf₂ hG hH hbound hgrad
    (fun i j y => hsecond i j j y) hΨ
  have hsection := hasPolynomiallyBoundedSecond_ouComposition hf hG hH hbound hgrad hsecond hΨ ht.le
  have hrestricted : ContDiffOn ℝ 1 F (Ioo (0 : ℝ) T ×ˢ univ) :=
    hF.mono (fun _ hp => ⟨hp.1.1, hp.2⟩)
  have h := hasDerivAt_ouSpaceTimeAverage_generator isOpen_Ioo ⟨ht, hT⟩
    (fun _ hs => hs.2) hrestricted hsection hC (N := 1)
    (fun s hs y => by simpa only [F, Function.comp_def, pow_one] using hdom s hs.1 y) x
  have htime (y : Fin n → ℝ) : fderiv ℝ F (t, y) (1, 0) =
      ∑ i, coordinateDerivative Ψ i (g y) * ouGenerator (fun z => g z i) y := by
    have hp : (t, y) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨ht, mem_univ _⟩
    have hdiff := (hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).differentiableAt_one
    have hder := ((hΨg y).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠
      0)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_ouFamily hf₂ y ht)
    rw [← deriv_spaceTime_left hdiff]
    change deriv (Ψ ∘ fun s => ouFamily f (s, y)) t = _
    rw [hder.deriv, concentration_fderiv_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hcancel : (fun y => fderiv ℝ F (t, y) (1, 0) -
      ouGenerator (fun z => F (t, z)) y) = fun y => -ouHessianContraction Ψ f t y := by
    funext y
    rw [htime]
    have hgen := ouGenerator_comp hΨg hg y
    change ouGenerator (fun z => F (t, z)) y = _ at hgen
    rw [hgen]
    dsimp only [ouHessianContraction, g, ouFamily]
    ring
  rw [hcancel] at h
  simpa only [ouAverage, integral_neg] using h


end EhrhardGaussian.Ehrhard

end
