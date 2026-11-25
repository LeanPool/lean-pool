/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothMax

/-!
# A scale-dependent binary regularized maximum

For a positive real scale `δ`, this module defines the pointwise binary operation
`g + δ P ((f - g) / δ)` associated with `SmoothMax.smoothMax`.  It proves only
its real-valued, same-domain pointwise calculus: monotonicity, exact agreement
with either branch outside the transition strip, and elementary bounds by the
ordinary maximum.  The final theorem specializes the existing `C²` complex
Hessian positivity calculation to this scaling.  It does not construct a
multi-chart or variable-domain gluing.
-/

@[expose] public section

open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.ScaledSmoothMax

open SmoothMax
open FirstPass FirstPass.MongeAmpere Complex

noncomputable section

/-- The binary regularized maximum at transition scale `δ`.

For `δ > 0`, it is `g + δ P ((f - g) / δ)` and differs from `max f g` only in
an order-`δ` transition strip. -/
def scaledSmoothMax {E : Type*} (δ : ℝ) (f g : E → ℝ) : E → ℝ :=
  fun z ↦ g z + δ * SmoothMax.posPart ((f z - g z) / δ)

@[simp]
theorem scaledSmoothMax_apply {E : Type*} (δ : ℝ) (f g : E → ℝ) (z : E) :
    scaledSmoothMax δ f g z = g z + δ * SmoothMax.posPart ((f z - g z) / δ) := rfl

/-- Positive rescaling reduces the scale-`δ` operation to `smoothMax`. -/
theorem scaledSmoothMax_eq_smul {E : Type*} {δ : ℝ} (hδ : 0 < δ) (f g : E → ℝ) :
    scaledSmoothMax δ f g = δ • smoothMax (δ⁻¹ • f) (δ⁻¹ • g) := by
  funext z
  simp only [scaledSmoothMax, smoothMax, Pi.smul_apply, smul_eq_mul,
    div_eq_inv_mul, mul_add, ← mul_sub]
  rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]

/-- The scale-`δ` regularized maximum is monotone in both branches. -/
theorem scaledSmoothMax_mono {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    {f f' g g' : E → ℝ} {z : E} (hf : f z ≤ f' z) (hg : g z ≤ g' z) :
    scaledSmoothMax δ f g z ≤ scaledSmoothMax δ f' g' z := by
  rw [scaledSmoothMax_eq_smul hδ, scaledSmoothMax_eq_smul hδ]
  change δ * smoothMax (δ⁻¹ • f) (δ⁻¹ • g) z ≤
    δ * smoothMax (δ⁻¹ • f') (δ⁻¹ • g') z
  apply mul_le_mul_of_nonneg_left
  · apply smoothMax_mono
    · simpa [Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hf (inv_nonneg.2 hδ.le)
    · simpa [Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hg (inv_nonneg.2 hδ.le)
  · exact hδ.le

/-- Above the positive transition strip, the left branch survives exactly. -/
theorem scaledSmoothMax_eq_left {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    {f g : E → ℝ} {z : E} (h : g z + δ ≤ f z) :
    scaledSmoothMax δ f g z = f z := by
  rw [scaledSmoothMax_apply, posPart_eq_self ((one_le_div hδ).2 (by linarith)),
    mul_div_cancel₀ _ hδ.ne']
  ring

/-- Below the negative transition strip, the right branch survives exactly. -/
theorem scaledSmoothMax_eq_right {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    {f g : E → ℝ} {z : E} (h : f z + δ ≤ g z) :
    scaledSmoothMax δ f g z = g z := by
  rw [scaledSmoothMax_apply, posPart_eq_zero ((div_le_iff₀ hδ).2 (by linarith))]
  ring

/-- Both input branches lie below the scale-`δ` regularized maximum. -/
theorem le_scaledSmoothMax_left {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    (f g : E → ℝ) (z : E) : f z ≤ scaledSmoothMax δ f g z := by
  have h := mul_le_mul_of_nonneg_left (SmoothMax.le_posPart ((f z - g z) / δ)) hδ.le
  rw [mul_div_cancel₀ _ hδ.ne'] at h
  rw [scaledSmoothMax_apply]
  linarith

/-- Both input branches lie below the scale-`δ` regularized maximum. -/
theorem le_scaledSmoothMax_right {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    (f g : E → ℝ) (z : E) : g z ≤ scaledSmoothMax δ f g z := by
  rw [scaledSmoothMax_apply]
  exact le_add_of_nonneg_right (mul_nonneg hδ.le (SmoothMax.posPart_nonneg _))

/-- The ordinary maximum is a lower bound for the scale-`δ` regularized maximum. -/
theorem max_le_scaledSmoothMax {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    (f g : E → ℝ) (z : E) : max (f z) (g z) ≤ scaledSmoothMax δ f g z := by
  exact max_le (le_scaledSmoothMax_left hδ f g z) (le_scaledSmoothMax_right hδ f g z)

/-- The scale-`δ` regularized maximum exceeds the ordinary maximum by at most `δ`. -/
theorem scaledSmoothMax_le_max_add {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    (f g : E → ℝ) (z : E) :
    scaledSmoothMax δ f g z ≤ max (f z) (g z) + δ := by
  rw [scaledSmoothMax_apply]
  rcases le_total (f z - g z) δ with h | h
  · have hP := mul_le_mul_of_nonneg_left
      (SmoothMax.posPart_le_one ((div_le_one hδ).2 h)) hδ.le
    linarith [le_max_right (f z) (g z)]
  · rw [posPart_eq_self ((one_le_div hδ).2 h), mul_div_cancel₀ _ hδ.ne']
    linarith [le_max_left (f z) (g z)]

/-- The two-sided pointwise approximation bound by the ordinary maximum. -/
theorem max_le_scaledSmoothMax_le_max_add {E : Type*} {δ : ℝ} (hδ : 0 < δ)
    (f g : E → ℝ) (z : E) :
    max (f z) (g z) ≤ scaledSmoothMax δ f g z ∧
      scaledSmoothMax δ f g z ≤ max (f z) (g z) + δ :=
  ⟨max_le_scaledSmoothMax hδ f g z, scaledSmoothMax_le_max_add hδ f g z⟩

/-- Positive complex-Hessian semidefiniteness is preserved by positive rescaling
of the binary regularized maximum.  This is a pointwise `C²` statement on one
fixed `ComplexModel n`; it is not a manifold gluing theorem. -/
theorem complexHessian_scaledSmoothMax_posSemidef {n : ℕ}
    {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hHf : (complexHessian f z).PosSemidef) (hHg : (complexHessian g z).PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    (complexHessian (scaledSmoothMax δ f g) z).PosSemidef := by
  have hf' : ContDiffAt ℝ 2 (δ⁻¹ • f) z := by
    simpa [Pi.smul_def] using hf.const_smul δ⁻¹
  have hg' : ContDiffAt ℝ 2 (δ⁻¹ • g) z := by
    simpa [Pi.smul_def] using hg.const_smul δ⁻¹
  have hHf' : (complexHessian (δ⁻¹ • f) z).PosSemidef := by
    rw [complexHessian_smul hf]
    exact hHf.smul (by exact_mod_cast (inv_pos.2 hδ).le)
  have hHg' : (complexHessian (δ⁻¹ • g) z).PosSemidef := by
    rw [complexHessian_smul hg]
    exact hHg.smul (by exact_mod_cast (inv_pos.2 hδ).le)
  have hsm : ContDiffAt ℝ 2 (smoothMax (δ⁻¹ • f) (δ⁻¹ • g)) z := by
    have hP : ContDiffAt ℝ 2 (SmoothMax.posPart ∘ ((δ⁻¹ • f) - (δ⁻¹ • g))) z :=
      (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z (hf'.sub hg')
    exact hg'.add hP
  rw [scaledSmoothMax_eq_smul hδ, complexHessian_smul hsm]
  exact (complexHessian_smoothMax_posSemidef hf' hg' hHf' hHg').smul
    (by exact_mod_cast hδ.le)

end

end SGPT.Foundations.Analysis.Pending.ScaledSmoothMax
