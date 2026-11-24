/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicMixedDensity

/-!
# The complex Hessian of a `C²` function under a holomorphic map

`HolomorphicMixedDensity.hessForm_comp_holomorphic` and `complexHessian_comp_holomorphic` state the
chain rule `H(p ∘ F)(y) = Jᵀ H(p)(F y) JBar` for a holomorphic `F` and a SMOOTH `p`.  The proof only
needs `p` to be `C²` near `F y`: the pullback formula for the exterior derivative
(`extDeriv_pullback`) asks for a differentiable one-form `dᶜp`.  This module records the `C²`
versions (`smoothDDC_comp_two`, `hessForm_comp_holomorphic_two`,
`complexHessian_comp_holomorphic_two`).

Consumer: the chart independence of the Kähler Laplacian `Δ_ω u = Re tr(H_ω⁻¹ H(u))` for
`u ∈ C^{2,α}(M)` (TN.4 B5 linear track L4: the Laplacian of a Kähler form as a realizable chartwise
operator, `ManifoldParametrix` / `ManifoldContinuity`).
-/

@[expose] public section

noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.HolomorphicHessianTwo

open FirstPass FirstPass.MongeAmpere HolomorphicMixedDensity

variable {k n : ℕ}

/-- `dᶜρ` is differentiable at a point near which `ρ` is `C²`. -/
theorem differentiableAt_smoothDc {ρ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hρ : ContDiffAt ℝ 2 ρ z) : DifferentiableAt ℝ (smoothDc ρ) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ ρ) z :=
    (hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ
      (fun y => (-1 / (4 * Real.pi) : ℝ) • (fderiv ℝ ρ y).comp (modelComplexStructure n)) z := by
    fun_prop
  exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ)
    (0 : Fin 1)).differentiableAt).comp z h1

/-- **`ddᶜ` commutes with holomorphic pullback for `C²` functions.** -/
theorem smoothDDC_comp_two {F : ComplexModel k → ComplexModel n} {ρ : ComplexModel n → ℝ}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hρ : ContDiffOn ℝ 2 ρ V) (hFV : MapsTo F U V)
    {z : ComplexModel k} (hz : z ∈ U) :
    smoothDDC (fun y => ρ (F y)) z =
      (smoothDDC ρ (F z)).compContinuousLinearMap (fderiv ℝ F z) := by
  have heq : smoothDc (fun y => ρ (F y)) =ᶠ[𝓝 z]
      (fun y => (smoothDc ρ (F y)).compContinuousLinearMap (fderiv ℝ F y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact HolomorphicDDC.smoothDc_comp
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (((hρ (F y) (hFV hy)).contDiffAt (hV.mem_nhds (hFV hy))).differentiableAt (by simp))
  apply heq.extDeriv_eq.trans
  exact extDeriv_pullback
    (differentiableAt_smoothDc ((hρ (F z) (hFV hz)).contDiffAt (hV.mem_nhds (hFV hz))))
    (((hF.restrict_scalars ℝ) z hz).contDiffAt (hU.mem_nhds hz))
    (by simp)

/-- **Chain rule for the complex Hessian of a `C²` function under a holomorphic map.** -/
theorem hessForm_comp_holomorphic_two {F : ComplexModel k → ComplexModel n}
    {p : ComplexModel n → ℝ} {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ 2 p V)
    (hFV : MapsTo F U V) {y : ComplexModel k} (hy : y ∈ U) (v w : ComplexModel k) :
    hessForm (fun x ↦ p (F x)) y v w = hessForm p (F y) (fderiv ℝ F y v) (fderiv ℝ F y w) := by
  have hFy : DifferentiableAt ℂ F y :=
    ((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hq2 : ContDiffAt ℝ 2 (fun x ↦ p (F x)) y :=
    ((hp.comp ((hF.restrict_scalars ℝ).of_le (by
      simp)) hFV) y hy).contDiffAt
      (hU.mem_nhds hy)
  have hp2 : ContDiffAt ℝ 2 p (F y) := (hp (F y) (hFV hy)).contDiffAt (hV.mem_nhds (hFV hy))
  have hnat (a b : ComplexModel k) :
      smoothDDC (fun x ↦ p (F x)) y ![a, b] =
        smoothDDC p (F y) ![fderiv ℝ F y a, fderiv ℝ F y b] := by
    have h := congrArg (fun A : (ComplexModel k) [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![a, b])
      (smoothDDC_comp_two hU hV hF hp hFV hy)
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
    rw [h]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hmapI : fderiv ℝ F y (I • w) = I • fderiv ℝ F y w := by
    rw [hFy.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ F y).map_smul I w
  rw [hessForm_eq_smoothDDC hq2, hessForm_eq_smoothDDC hp2, hnat, hnat, hmapI]

/-- **`H(p ∘ F) = Jᵀ H(p) JBar`** for a holomorphic `F` and a `C²` function `p`. -/
theorem complexHessian_comp_holomorphic_two {F : ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} {U V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hp : ContDiffOn ℝ 2 p V) (hFV : MapsTo F U V)
    {y : ComplexModel n} (hy : y ∈ U) :
    complexHessian (fun x ↦ p (F x)) y =
      (jacobianMatrix F y).transpose * complexHessian p (F y) *
        (jacobianMatrix F y).map (starRingEnd ℂ) := by
  ext j k
  rw [complexHessian_eq_hessForm, hessForm_comp_holomorphic_two hU hV hF hp hFV hy,
    hessForm_eq_sum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacobianMatrix,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Complex.star_def]
  ring

end SGPT.Foundations.Analysis.Pending.HolomorphicHessianTwo
