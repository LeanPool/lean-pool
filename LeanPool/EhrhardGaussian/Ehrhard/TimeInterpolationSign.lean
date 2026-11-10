/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimeNonlinearCommutation
public import LeanPool.EhrhardGaussian.Ehrhard.InterpolationSign

/-! The covariance matrix condition determines the sign of the interpolation integrand. -/

@[expose] public noncomputable section

open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The matrix and gradient conditions imply that the time-dependent commutation integrand is
nonpositive after pulling back coordinate derivatives along a Gaussian factor. -/
theorem time_interpolation_integrand_nonpos {n k : ℕ}
    (J : ℝ × (Fin k → ℝ) → ℝ) (f : Fin k → (Fin n → ℝ) → ℝ)
    (t : ℝ) (y : Fin n → ℝ) (C : Matrix (Fin k) (Fin n) ℝ) (v : Fin k → ℝ)
    (hshape : ∀ i j, coordinateDerivative (fun z => ouAverage (f i) z t) j y = v i * C i j)
    {D : Matrix (Fin k) (Fin k) ℝ} {K : ℝ} (hK : 0 < K)
    (htime : fderiv ℝ J (t, ouFamily f (t, y)) (1, 0) ≤ 0)
    (hPSD : (((C * Cᵀ) ⊙ coordinateHessian (fun z => J (t, z)) (ouFamily f (t, y))) -
      (K * fderiv ℝ J (t, ouFamily f (t, y)) (1, 0)) • D).PosSemidef)
    (hgradient : v ⬝ᵥ (D *ᵥ v) ≤ 1 / K) :
    fderiv ℝ J (t, ouFamily f (t, y)) (1, 0) -
      ouHessianContraction (fun z => J (t, z)) f t y ≤ 0 := by
  have heq : ouHessianContraction (fun z => J (t, z)) f t y =
      v ⬝ᵥ (((C * Cᵀ) ⊙ coordinateHessian (fun z => J (t, z)) (ouFamily f (t, y))) *ᵥ v) := by
    change (∑ i, ∑ l, coordinateHessian (fun z => J (t, z)) (ouFamily f (t, y)) i l *
      ∑ j, coordinateDerivative (fun z => ouAverage (f i) z t) j y *
        coordinateDerivative (fun z => ouAverage (f l) z t) j y) = _
    simp_rw [hshape]
    exact gram_hessian_contraction C _ v
  rw [heq]
  exact corrected_interpolation_sign htime hK hPSD v hgradient

end EhrhardGaussian.Ehrhard

end
