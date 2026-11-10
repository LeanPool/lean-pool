/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUFamily
public import LeanPool.EhrhardGaussian.Ehrhard.CompactDerivativeBounds
public import LeanPool.EhrhardGaussian.Ehrhard.BoundedComposition

/-! # Regularity and domination for the nonlinear OU family -/

@[expose] public noncomputable section

open Set
open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- Ornstein–Uhlenbeck averaging preserves a uniform gradient bound for each coordinate derivative.
-/
theorem abs_coordinateDerivative_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) {G : ℝ}
    (hgrad : ∀ y, ‖fderiv ℝ F y‖ ≤ G) (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (j : Fin n) : |coordinateDerivative (fun y => ouAverage F y t) j x| ≤ G := by
  have h := norm_fderiv_ouAverage_le hF hgrad x ht
  simpa only [coordinateDerivative, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
    ((fderiv ℝ (fun y => ouAverage F y t) x).le_opNorm (Pi.single j 1)).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))

/-- Ornstein–Uhlenbeck averaging preserves uniform bounds on second coordinate derivatives. -/
theorem abs_secondCoordinateDerivative_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) {H : ℝ}
    (hsecond : ∀ i j y, |coordinateDerivative (coordinateDerivative F i) j y| ≤ H)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) (i j : Fin n) :
    |coordinateDerivative (coordinateDerivative (fun y => ouAverage F y t) i) j x| ≤ H := by
  rw [secondCoordinateDerivative_ouAverage hF, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have he : Real.exp (-t) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  exact (mul_le_mul he (abs_ouAverage_le (hsecond i j) x t) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul _)

/-- A smooth composition of an Ornstein–Uhlenbeck family is continuously differentiable at positive
times. -/
theorem contDiffOn_ouComposition {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i)) {a b : ℝ}
    (hbound : ∀ i y, f i y ∈ Icc a b) {Ψ : (Fin k → ℝ) → ℝ}
    (hΨ : ∀ z, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 Ψ z) :
    ContDiffOn ℝ 1 (Ψ ∘ ouFamily f) (Ioi (0 : ℝ) ×ˢ univ) := by
  intro p hp
  exact ((hΨ _ (ouFamily_mem_Icc hf hbound p.2 p.1)).of_le (by norm_num)).comp_contDiffWithinAt p
    (contDiffOn_ouFamily hf p hp)

/-- The compact range discharges every spatial growth condition in the
nonlinear backward-time differentiation theorem. -/
theorem hasPolynomiallyBoundedSecond_ouComposition {n k : ℕ}
    {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i))
    {a b G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc a b)
    (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (f i) j) l y| ≤ H)
    {Ψ : (Fin k → ℝ) → ℝ}
    (hΨ : ∀ z, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 Ψ z)
    {t : ℝ} (ht : 0 ≤ t) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun y => Ψ (ouFamily f (t, y))) := by
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hf i)
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf₂ i)
  obtain ⟨M, hM, hv, _, hg, hh⟩ :=
    IsCompact.exists_bound_secondDerivatives (isCompact_probabilitySubbox a b) hΨ
  have hrange (y) := ouFamily_mem_Icc hf₁ hbound y t
  exact hasPolynomiallyBoundedSecond_comp_of_bounded
    (fun y => hΨ _ (hrange y)) (contDiff_ouFamily_space hf t) hM hG hH
    (fun y => hv _ (hrange y)) (fun i y => hg i _ (hrange y))
    (fun i j y => hh i j _ (hrange y))
    (fun i j y => abs_coordinateDerivative_ouAverage_le (hf₁ i) (hgrad i) y ht j)
    (fun i j l y => abs_secondCoordinateDerivative_ouAverage_le (hf₂ i) (hsecond i) y ht j l)

/-- A single linear bound in the space variable dominates the actual
nonlinear space-time family uniformly over every positive time. -/
theorem exists_ouComposition_spaceTime_bound {n k : ℕ}
    {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    {a b G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc a b)
    (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j y, |coordinateDerivative (coordinateDerivative (f i) j) j y| ≤ H)
    {Ψ : (Fin k → ℝ) → ℝ}
    (hΨ : ∀ z, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 Ψ z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ y : Fin n → ℝ,
      |Ψ (ouFamily f (t, y))| + ‖fderiv ℝ (Ψ ∘ ouFamily f) (t, y)‖ ≤ C * (1 + ‖y‖) := by
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i)
  obtain ⟨M, hM, hv, hd, _, _⟩ :=
    IsCompact.exists_bound_secondDerivatives (isCompact_probabilitySubbox a b) hΨ
  let B := max |a| |b|
  let A := B + (n : ℝ) * H + G
  have hB : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hvalue (i) (y) : |f i y| ≤ B := abs_le_max_abs_abs (hbound i y).1 (hbound i y).2
  refine ⟨M * (1 + A), by positivity, ?_⟩
  intro t ht y
  have hrange := ouFamily_mem_Icc hf₁ hbound y t
  have hp : (t, y) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨ht, mem_univ _⟩
  have hdiff := (contDiffOn_ouFamily hf₁).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have houter := (hΨ _ hrange).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hnorm : ‖fderiv ℝ (Ψ ∘ ouFamily f) (t, y)‖ ≤ M * (A * (1 + ‖y‖)) := by
    rw [fderiv_comp _ houter hdiff.differentiableAt_one]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hd _ hrange)
        (norm_fderiv_ouFamily_le hf hB hG hH hvalue hgrad hsecond ht y)
        (norm_nonneg _) hM)
  calc
    _ ≤ M + M * (A * (1 + ‖y‖)) := add_le_add (hv _ hrange) hnorm
    _ ≤ M * (1 + A) * (1 + ‖y‖) := by
      have h := mul_nonneg hM (norm_nonneg y)
      nlinarith only [h]

end EhrhardGaussian.Ehrhard

end
