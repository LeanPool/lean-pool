/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GeneratorChainRule

/-! # Polynomial growth of a bounded smooth composition -/

@[expose] public noncomputable section

open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- The absolute value of a finite sum is bounded by the number of terms times a common bound. -/
theorem abs_sum_fin_le {k : ℕ} {v : Fin k → ℝ} {C : ℝ}
    (hv : ∀ i, |v i| ≤ C) : |∑ i, v i| ≤ (k : ℝ) * C := by
  calc
    _ ≤ ∑ i, |v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, C := Finset.sum_le_sum fun i _ => hv i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Bounded first and second derivatives of the factors imply the intrinsic
polynomial growth condition used for Gaussian integration by parts. The outer
function only needs to be smooth on the range of the inner map. -/
theorem hasPolynomiallyBoundedSecond_comp_of_bounded {n k : ℕ}
    {Ψ : (Fin k → ℝ) → ℝ} {g : (Fin n → ℝ) → (Fin k → ℝ)}
    (hΨ : ∀ y, ContDiffAt ℝ 2 Ψ (g y)) (hg : ContDiff ℝ 2 g)
    {M G H : ℝ} (hM : 0 ≤ M) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hvalue : ∀ y, |Ψ (g y)| ≤ M)
    (hgrad : ∀ i y, |coordinateDerivative Ψ i (g y)| ≤ M)
    (hhess : ∀ i j y, |coordinateDerivative (coordinateDerivative Ψ i) j (g y)| ≤ M)
    (hggrad : ∀ i j y, |coordinateDerivative (fun z => g z i) j y| ≤ G)
    (hghess : ∀ i j l y,
      |coordinateDerivative (coordinateDerivative (fun z => g z i) j) l y| ≤ H) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (Ψ ∘ g) := by
  let C := M + (k : ℝ) * M * G + (k : ℝ) * ((k : ℝ) * M * G * G + M * H)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hA : 0 ≤ (k : ℝ) * M * G := by positivity
  have hB : 0 ≤ (k : ℝ) * ((k : ℝ) * M * G * G + M * H) := by positivity
  have hg' := hg.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hΨ' (y) := (hΨ y).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  refine ⟨contDiff_iff_contDiffAt.mpr (fun y => (hΨ y).comp y hg.contDiffAt),
    C, hC, 0, ?_, ?_, ?_⟩
  · intro y
    simp only [pow_zero, mul_one]
    exact (hvalue y).trans (by dsimp only [C]; linarith only [hA, hB])
  · intro j y
    simp only [pow_zero, mul_one]
    rw [coordinateDerivative_comp (hΨ' y) (hg' y) j]
    have hb := abs_sum_fin_le (fun i => show
        |coordinateDerivative Ψ i (g y) * coordinateDerivative (fun z => g z i) j y| ≤ M * G by
      rw [abs_mul]
      exact mul_le_mul (hgrad i y) (hggrad i j y) (abs_nonneg _) hM)
    exact hb.trans (by dsimp only [C]; nlinarith only [hM, hB])
  · intro j l y
    simp only [pow_zero, mul_one]
    rw [mixedSecondCoordinateDerivative_comp hΨ hg]
    have hinner (i : Fin k) :
        |∑ a, coordinateDerivative (coordinateDerivative Ψ i) a (g y) *
          coordinateDerivative (fun z => g z a) l y| ≤ (k : ℝ) * (M * G) := by
      apply abs_sum_fin_le
      intro a
      rw [abs_mul]
      exact mul_le_mul (hhess i a y) (hggrad a l y) (abs_nonneg _) hM
    have hb := abs_sum_fin_le (fun i => show
        |(∑ a, coordinateDerivative (coordinateDerivative Ψ i) a (g y) *
            coordinateDerivative (fun z => g z a) l y) *
            coordinateDerivative (fun z => g z i) j y +
          coordinateDerivative Ψ i (g y) *
            coordinateDerivative (coordinateDerivative (fun z => g z i) j) l y| ≤
          (k : ℝ) * M * G * G + M * H by
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      exact add_le_add
        ((mul_le_mul (hinner i) (hggrad i j y) (abs_nonneg _) (by positivity)).trans_eq (by ring))
        (mul_le_mul (hgrad i y) (hghess i j l y) (abs_nonneg _) hM))
    exact hb.trans (by dsimp only [C]; linarith only [hM, hA])

end EhrhardGaussian.Ehrhard

end
