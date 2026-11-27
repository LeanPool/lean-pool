/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.ApproxIdentity
public import Mathlib.MeasureTheory.Integral.Pi

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Tensor kernels on `ℝ^d`

On `ℝ^d = Fin d → ℝ` with Lebesgue measure, the **tensor product** of one-dimensional kernels
`K_0, …, K_{d-1} : ℝ → ℂ` is `(⊗K)(x) = ∏_i K_i(x_i)` (`Rd.tensorKernel`). Tensor products of
integrable kernels are integrable with `∫ ⊗K = ∏_i ∫ K_i` and `‖⊗K‖_1 = ∏_i ‖K_i‖_1` (Fubini,
Mathlib's `integral_fintype_prod_eq_prod`), and the operations behind the function spaces of
dominating mixed smoothness act coordinatewise:

* convolution, `(⊗K) ⋆ (⊗K') = ⊗(K_i ⋆ K'_i)` (`Rd.conv_tensorKernel`);
* dilation, `(⊗K)_c = ⊗((K_i)_c)` (`Rd.dilate_tensorKernel`);
* sums over boxes, `∑_{k ∈ ∏_i t_i} ⊗(K_i(k_i)) = ⊗(∑_{j ∈ t_i} K_i(j))`
  (`Rd.sum_tensorKernel_piFinset`);
* diagonal changes of variables: for `a_i > 0`,
  `∫ (⊗φ)(z) f(x - (a_i z_i)_i) dz = ((⊗ φ_i^{(1/a_i)}) ⋆ f)(x)` with `φ^{(c)}(t) = c φ(c t)`
  (`Rd.integral_tensorKernel_mul_comp_eq_conv`), since the diagonal map scales Lebesgue measure
  by its determinant `∏_i a_i` (Mathlib's `Real.map_linearMap_volume_pi_eq_smul_volume_pi`).

Convolutions with tensor kernels are `d`-dimensional convolutions, so Young's inequality, the
associativity of convolution and the approximate identities of
`FunctionSpaces.Analysis.Fourier.Convolution` and `FunctionSpaces.Analysis.Fourier.ApproxIdentity`
apply to them without change.
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal

namespace Rd

variable {d : ℕ}

/-- The **tensor product** `(⊗K)(x) = ∏_i K_i(x_i)` of one-dimensional kernels. -/
def tensorKernel (K : Fin d → ℝ → ℂ) (x : Fin d → ℝ) : ℂ := ∏ i, K i (x i)

/-- `(⊗K)(x) = ∏_i K_i(x_i)`. -/
theorem tensorKernel_apply (K : Fin d → ℝ → ℂ) (x : Fin d → ℝ) :
    tensorKernel K x = ∏ i, K i (x i) := rfl

/-- Tensor products of integrable kernels are integrable (Mathlib's `Integrable.fintype_prod`). -/
theorem integrable_tensorKernel {K : Fin d → ℝ → ℂ} (hK : ∀ i, Integrable (K i)) :
    Integrable (tensorKernel K) :=
  Integrable.fintype_prod (μ := fun _ => volume) hK

/-- Tensor products of continuous kernels are continuous. -/
theorem continuous_tensorKernel {K : Fin d → ℝ → ℂ} (hK : ∀ i, Continuous (K i)) :
    Continuous (tensorKernel K) :=
  continuous_finsetProd _ fun i _ => (hK i).comp (continuous_apply i)

/-- **The integral of a tensor product**: `∫ ⊗K = ∏_i ∫ K_i` (Fubini, Mathlib's
`integral_fintype_prod_eq_prod`). -/
theorem integral_tensorKernel (K : Fin d → ℝ → ℂ) :
    ∫ x, tensorKernel K x = ∏ i, ∫ t, K i t :=
  integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ) K

/-- **The `L_1` norm of a tensor product**: `‖⊗K‖_1 = ∏_i ‖K_i‖_1`. -/
theorem lintegral_enorm_tensorKernel {K : Fin d → ℝ → ℂ} (hK : ∀ i, Integrable (K i)) :
    ∫⁻ x, ‖tensorKernel K x‖ₑ = ∏ i, ∫⁻ t, ‖K i t‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_eNorm (integrable_tensorKernel hK)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_eNorm (hK _)]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg fun _ => norm_nonneg _]
  congr 1
  simp only [tensorKernel, norm_prod]
  exact integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ) (fun i t => ‖K i t‖)

/-- `‖⊗K‖_1 = ∏_i ‖K_i‖_1` with `eLpNorm`. -/
theorem eLpNorm_tensorKernel_one {K : Fin d → ℝ → ℂ} (hK : ∀ i, Integrable (K i)) :
    eLpNorm (tensorKernel K) 1 volume = ∏ i, eLpNorm (K i) 1 volume := by
  rw [eLpNorm_one_eq_lintegral_eNorm (integrable_tensorKernel hK).aestronglyMeasurable,
    lintegral_enorm_tensorKernel hK]
  exact Finset.prod_congr rfl fun i _ =>
    (eLpNorm_one_eq_lintegral_eNorm (hK i).aestronglyMeasurable).symm

/-- **Convolution of tensor products**: `(⊗K) ⋆ (⊗K') = ⊗(K_i ⋆ K'_i)` (Fubini). -/
theorem conv_tensorKernel (K K' : Fin d → ℝ → ℂ) :
    conv (tensorKernel K) (tensorKernel K') volume =
      tensorKernel fun i => conv (K i) (K' i) volume := by
  funext x
  rw [conv_apply, tensorKernel]
  simp only [conv_apply]
  have h : ∀ y : Fin d → ℝ, tensorKernel K y * tensorKernel K' (x - y) =
      ∏ i, K i (y i) * K' i (x i - y i) := fun y => by
    simp [tensorKernel, Finset.prod_mul_distrib]
  simp_rw [h]
  exact integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ)
    (fun i t => K i t * K' i (x i - t))

/-- **Dilations of tensor products**: `(⊗K)_c = ⊗((K_i)_c)`, since `c^d = ∏_i c`. -/
theorem dilate_tensorKernel (c : ℝ) (K : Fin d → ℝ → ℂ) :
    dilate c (tensorKernel K) = tensorKernel fun i => dilate c (K i) := by
  funext x
  simp only [dilate, tensorKernel, finrank_fin_fun, finrank_self, pow_one, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

/-- **Sums of tensor products over boxes**:
`∑_{k ∈ ∏_i t_i} ⊗(K_i(k_i)) = ⊗(∑_{j ∈ t_i} K_i(j))`. -/
theorem sum_tensorKernel_piFinset {ι : Type*} (t : Fin d → Finset ι) (K : Fin d → ι → ℝ → ℂ) :
    ∑ k ∈ Fintype.piFinset t, tensorKernel (fun i => K i (k i)) =
      tensorKernel fun i => ∑ j ∈ t i, K i j := by
  funext x
  simp only [Finset.sum_apply, tensorKernel]
  rw [Finset.prod_univ_sum]

/-! ### Diagonal changes of variables -/

/-- The diagonal linear map `z ↦ (a_i z_i)_i`. -/
noncomputable def diagMap (a : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] Fin d → ℝ :=
  Matrix.toLin' (Matrix.diagonal a)

/-- `(diagMap a z)_i = a_i z_i`. -/
theorem diagMap_apply (a : Fin d → ℝ) (z : Fin d → ℝ) : diagMap a z = fun i => a i * z i := by
  funext i
  simp [diagMap, Matrix.mulVec_diagonal]

/-- The determinant of the diagonal map is `∏_i a_i`. -/
theorem det_diagMap (a : Fin d → ℝ) : LinearMap.det (diagMap a) = ∏ i, a i := by
  rw [diagMap, LinearMap.det_toLin', Matrix.det_diagonal]

/-- For nonzero `a_i` the diagonal map is a measurable equivalence. -/
noncomputable def diagEquiv {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  MeasurableEquiv.piCongrRight fun i => MeasurableEquiv.mulLeft₀ (a i) (ha i)

/-- `diagEquiv z = (a_i z_i)_i`. -/
theorem diagEquiv_apply {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) (z : Fin d → ℝ) :
    diagEquiv ha z = fun i => a i * z i := rfl

/-- **Diagonal changes of variables**: for `a_i > 0`,
`∫ F((a_i z_i)_i) dz = (∏_i a_i)⁻¹ ∫ F` (Mathlib's
`Real.map_linearMap_volume_pi_eq_smul_volume_pi`). -/
theorem integral_comp_diagMap {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) (F : (Fin d → ℝ) → ℂ) :
    ∫ z : Fin d → ℝ, F (fun i => a i * z i) = ((∏ i, a i)⁻¹ : ℝ) • ∫ y, F y := by
  have hdet : LinearMap.det (diagMap a) ≠ 0 := by
    rw [det_diagMap]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (ha i).ne'
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have he := (diagEquiv fun i => (ha i).ne').measurableEmbedding
  have hcoe : ⇑(diagEquiv fun i => (ha i).ne') = ⇑(diagMap a) := by
    funext z
    rw [diagMap_apply, diagEquiv_apply]
  calc ∫ z : Fin d → ℝ, F (fun i => a i * z i)
      = ∫ z, F ((diagEquiv fun i => (ha i).ne') z) := by simp_rw [diagEquiv_apply]
    _ = ∫ y, F y ∂(Measure.map (diagEquiv fun i => (ha i).ne') volume) := (he.integral_map F).symm
    _ = ∫ y, F y ∂(Measure.map (diagMap a) volume) := by rw [hcoe]
    _ = ((∏ i, a i)⁻¹ : ℝ) • ∫ y, F y := by
        rw [hmap, integral_smul_measure, det_diagMap, ENNReal.toReal_ofReal (abs_nonneg _),
          abs_of_pos (inv_pos.2 hpos)]

/-- **Anisotropic substitution** in a tensor integral: for `a_i > 0`,
`∫ (⊗φ)(z) f(x - (a_i z_i)_i) dz = ((⊗ φ_i^{(1/a_i)}) ⋆ f)(x)` with `φ^{(c)}(t) = c φ(c t)`. -/
theorem integral_tensorKernel_mul_comp_eq_conv (φ : Fin d → ℝ → ℂ) {a : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    ∫ z, tensorKernel φ z * f (x - fun i => a i * z i) =
      conv (tensorKernel fun i => dilate (a i)⁻¹ (φ i)) f volume x := by
  have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [conv_apply]
  have h := integral_comp_diagMap ha
    (fun y => tensorKernel (fun i => dilate (a i)⁻¹ (φ i)) y * f (x - y))
  have hterm : ∀ z : Fin d → ℝ,
      tensorKernel (fun i => dilate (a i)⁻¹ (φ i)) (fun i => a i * z i) =
        (((∏ i, a i)⁻¹ : ℝ) : ℂ) * tensorKernel φ z := fun z => by
    simp only [tensorKernel, dilate, finrank_self, pow_one, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    congr 1
    · push_cast
      rw [Finset.prod_inv_distrib]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_assoc, inv_mul_cancel₀ (ha i).ne', one_mul]
  simp_rw [hterm, mul_assoc] at h
  rw [integral_const_mul] at h
  have hne : (((∏ i, a i)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_pos.2 hpos).ne'
  rw [Complex.real_smul] at h
  exact mul_left_cancel₀ hne h

end Rd
