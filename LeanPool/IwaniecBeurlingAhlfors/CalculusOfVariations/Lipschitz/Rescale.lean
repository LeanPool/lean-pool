/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient

/-!
# Rescaled test maps

`∇ (x ↦ k⁻¹ φ (k x)) = (∇φ) (k x)`; the rescaled copy `rescaleMap ψ c s = s ψ (s⁻¹ (· − c))`, its
Lipschitz constant, its gradient and the change of variables `y = s⁻¹ (x − c)`.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- `∇ (x ↦ k⁻¹ φ (k x)) = (∇φ) (k x)`. -/
lemma rd_grad_rescale (φ : (Fin m → ℝ) → Fin d → ℝ) {k : ℝ} (hk : k ≠ 0)
    (x : Fin m → ℝ) : grad (fun y => k⁻¹ • φ (k • y)) x = grad φ (k • x) := by
  ext i j
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => k⁻¹ * φ (k • y) i) = k⁻¹ • ((fun y => φ y i) <| k • ·) := rfl
  have h2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun y => φ y i) (x := x) k
  rw [this, fderiv_const_smul_field, Pi.smul_apply]
  erw [h2]
  simp only [smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-! ### Rescaled test maps -/

/-- The rescaled copy `x ↦ s ψ (s⁻¹ (x - c))` of `ψ`, supported in `c + s · supp ψ`. -/
noncomputable def rescaleMap (ψ : (Fin m → ℝ) → Fin d → ℝ) (c : Fin m → ℝ) (s : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun x => s • ψ (s⁻¹ • (x - c))

theorem rescaleMap_lipschitz {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hψ : LipschitzWith K ψ)
    (c : Fin m → ℝ) {s : ℝ} (hs : 0 < s) : LipschitzWith K (rescaleMap ψ c s) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [rescaleMap, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
  have := hψ.dist_le_mul (s⁻¹ • (x - c)) (s⁻¹ • (y - c))
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hs).le,
    sub_sub_sub_cancel_right] at this
  calc s * ‖ψ (s⁻¹ • (x - c)) - ψ (s⁻¹ • (y - c))‖ ≤ s * (K * (s⁻¹ * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left this hs.le
    _ = K * ‖x - y‖ := by field_simp

theorem rescaleMap_grad (ψ : (Fin m → ℝ) → Fin d → ℝ) (c : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (x : Fin m → ℝ) : grad (rescaleMap ψ c s) x = grad ψ (s⁻¹ • (x - c)) := by
  ext i k
  change fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x (Pi.single k 1) =
    fderiv ℝ (fun y => ψ y i) (s⁻¹ • (x - c)) (Pi.single k 1)
  have e : fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x =
      s • (s⁻¹ • fderiv ℝ (fun w => ψ w i) (s⁻¹ • (x - c))) := by
    calc fderiv ℝ (fun y => (s • ψ (s⁻¹ • (y - c))) i) x
        = fderiv ℝ (s • fun y => ψ (s⁻¹ • (y + -c)) i) x := by
          congr 1
      _ = s • fderiv ℝ (fun z => ψ (s⁻¹ • z) i) (x + -c) := by
          rw [fderiv_const_smul_field, Pi.smul_apply,
            fderiv_comp_add_right (f := fun z => ψ (s⁻¹ • z) i)]
      _ = s • (s⁻¹ • fderiv ℝ (fun w => ψ w i) (s⁻¹ • (x - c))) := by
          rw [fderiv_comp_smul (f := fun w => ψ w i), sub_eq_add_neg]
  rw [e]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem rescaleMap_eq_zero {ψ : (Fin m → ℝ) → Fin d → ℝ} {S : Set (Fin m → ℝ)}
    (hψ : ∀ y ∉ S, ψ y = 0) (c : Fin m → ℝ) (s : ℝ) {x : Fin m → ℝ}
    (hx : s⁻¹ • (x - c) ∉ S) : rescaleMap ψ c s x = 0 := by
  simp [rescaleMap, hψ _ hx]

/-- The change of variables `y = s⁻¹ (x - c)`. -/
theorem cv_integral_comp_affine (G : (Fin m → ℝ) → ℝ) (c : Fin m → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, G (s⁻¹ • (x - c)) = s ^ m * ∫ y, G y := by
  rw [integral_sub_right_eq_self (fun x => G (s⁻¹ • x)) c, Measure.integral_comp_smul,
    Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos hs m), smul_eq_mul]

end CalculusOfVariations
