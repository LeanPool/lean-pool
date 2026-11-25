/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

-- Modifications: adapted documentation and wrapped declarations in the SGPT.Foundations.Analysis
-- namespace
-- and changed the KahlerForm import to the project-local module.
-- Source: https://github.com/zblore/csd-lean4/blob/c63273eceeb1c36c937eccfdf24795043666204f/CsdLean4/Mathlib/Analysis/InnerProductSpace/KahlerClosed.lean

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Upstream.KahlerForm
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Closedness of the flat Hermitian fundamental form

The imaginary part of the complex inner product is bundled as a continuous
alternating real two-form. Cauchy–Schwarz supplies continuity. The corresponding
constant differential form on the vector space has zero exterior derivative.

This is normed-space exterior calculus, not a construction of forms or currents
on an arbitrary complex manifold. No potential or `dᶜ` normalization is defined.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis

open ContinuousAlternatingMap

/-! ### Generic: constant differential forms are closed -/

section ExtDerivConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

/-- The exterior derivative of a constant differential form vanishes (pointwise
form). `extDeriv` is the alternatization of `fderiv`, and the
derivative of a constant is `0`. -/
theorem extDeriv_const_apply (c : E [⋀^Fin n]→L[𝕜] F) (x : E) :
    extDeriv (fun _ : E => c) x = 0 := by
  rw [extDeriv, fderiv_fun_const, ← alternatizeUncurryFinCLM_apply]
  exact map_zero _

/-- The exterior derivative of a constant differential form vanishes. -/
theorem extDeriv_const (c : E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (fun _ : E => c) = 0 :=
  funext (extDeriv_const_apply c)

end ExtDerivConst

/-! ### The fundamental form as a continuous alternating 2-form -/

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Right-slot additivity of the fundamental form (companion to
`fundamentalForm_add_left`). -/
theorem fundamentalForm_add_right (u v v' : E) :
    fundamentalForm u (v + v') = fundamentalForm u v + fundamentalForm u v' := by
  simp [fundamentalForm, inner_add_right]

/-- Right-slot real homogeneity of the fundamental form (companion to
`fundamentalForm_real_smul_left`). -/
theorem fundamentalForm_real_smul_right (r : ℝ) (u v : E) :
    fundamentalForm u (r • v) = r * fundamentalForm u v := by
  have hcast : (r • v : E) = ((r : ℂ)) • v := by
    rw [← smul_one_smul ℂ r v, Complex.real_smul, mul_one]
  rw [hcast]
  simp only [fundamentalForm, inner_smul_right, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Cauchy–Schwarz bound for the fundamental form: `|ω u v| ≤ ‖u‖ * ‖v‖`. -/
theorem abs_fundamentalForm_le (u v : E) : |fundamentalForm u v| ≤ ‖u‖ * ‖v‖ :=
  calc |fundamentalForm u v| = |(inner ℂ u v).im| := rfl
    _ ≤ ‖(inner ℂ u v : ℂ)‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v

/-- The fundamental form as a bundled `ℝ`-bilinear map. -/
noncomputable def fundamentalFormBilin : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ fundamentalForm
    fundamentalForm_add_left
    (fun r u v => fundamentalForm_real_smul_left r u v)
    fundamentalForm_add_right
    (fun r u v => fundamentalForm_real_smul_right r u v)

/-- The fundamental form as a continuous `ℝ`-bilinear map (Cauchy–Schwarz gives
the bound). -/
noncomputable def fundamentalFormCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ fundamentalFormBilin 1 fun u v => by
    simpa [fundamentalFormBilin, Real.norm_eq_abs] using abs_fundamentalForm_le u v

@[simp] lemma fundamentalFormCLM_apply (u v : E) :
    fundamentalFormCLM u v = fundamentalForm u v := rfl

/-- The fundamental form as a continuous multilinear map on `Fin 2 → E`
(uncurried through `continuousMultilinearCurryFin1`). -/
noncomputable def fundamentalFormMulti :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearIsometry.toContinuousLinearMap).comp
      fundamentalFormCLM)

@[simp] lemma fundamentalFormMulti_apply (v : Fin 2 → E) :
    fundamentalFormMulti v = fundamentalForm (v 0) (v 1) := by
  simp [fundamentalFormMulti, Fin.tail]

/-- **The fundamental 2-form**: `ω u v = im ⟪u,v⟫` as a continuous alternating
2-form on `E` (alternating by `fundamentalForm_self`). -/
noncomputable def fundamentalFormAlt : E [⋀^Fin 2]→L[ℝ] ℝ where
  toContinuousMultilinearMap := fundamentalFormMulti
  map_eq_zero_of_eq' := by
    intro v i j hv hne
    fin_cases i <;> fin_cases j <;>
      simp_all [fundamentalFormMulti_apply]

@[simp] lemma fundamentalFormAlt_apply (v : Fin 2 → E) :
    fundamentalFormAlt v = fundamentalForm (v 0) (v 1) :=
  fundamentalFormMulti_apply v

/-- The constant fundamental two-form has zero exterior derivative at every point. -/
theorem extDeriv_fundamentalFormAlt (x : E) :
    extDeriv (fun _ : E => (fundamentalFormAlt : E [⋀^Fin 2]→L[ℝ] ℝ)) x = 0 :=
  extDeriv_const_apply _ x

/-- ★ Flat closedness of the fundamental form, function form: `dω = 0`. -/
theorem extDeriv_fundamentalFormAlt_eq_zero :
    extDeriv (fun _ : E => (fundamentalFormAlt : E [⋀^Fin 2]→L[ℝ] ℝ)) = 0 :=
  extDeriv_const _

end Kahler

end SGPT.Foundations.Analysis
