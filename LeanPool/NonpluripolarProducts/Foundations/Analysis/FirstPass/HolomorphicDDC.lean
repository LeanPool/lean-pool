/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ClosedRealOneOneForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Naturality of the normalized smooth complex differential

These identities use the actual real exterior derivative and the real derivative
of a holomorphic map. Smoothness is required only on the specified open domains;
values chosen outside those domains play no role. No current pullback or
plurisubharmonic pullback theorem is assumed.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

noncomputable section

variable {k n : ℕ}

/-- The normalized one-form commutes with holomorphic pullback at a point. -/
theorem smoothDc_comp {F : ComplexModel k → ComplexModel n}
    {ρ : ComplexModel n → ℝ} {z : ComplexModel k}
    (hF : DifferentiableAt ℂ F z) (hρ : DifferentiableAt ℝ ρ (F z)) :
    smoothDc (fun y => ρ (F y)) z =
      (smoothDc ρ (F z)).compContinuousLinearMap (fderiv ℝ F z) := by
  change smoothDc (ρ ∘ F) z = _
  ext v
  rw [smoothDc_apply, fderiv_comp z hρ (hF.restrictScalars ℝ)]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smoothDc_apply]
  rw [hF.fderiv_restrictScalars ℝ]
  exact congrArg (fun w => (-1 / (4 * Real.pi)) * fderiv ℝ ρ (F z) w)
    ((fderiv ℂ F z).map_smul Complex.I (v 0))

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
    exact smoothDc_comp
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (((hρ (F y) (hFV hy)).contDiffAt (hV.mem_nhds (hFV hy))).differentiableAt (by simp))
  apply heq.extDeriv_eq.trans
  exact extDeriv_pullback
    (differentiableAt_smoothDc ((hρ (F z) (hFV hz)).contDiffAt (hV.mem_nhds (hFV hz))))
    (((hF.restrict_scalars ℝ) z hz).contDiffAt (hU.mem_nhds hz))
    (by simp)

/-- The complete normalized two-form, not just its diagonal values, commutes
with a smooth holomorphic map between open sets. -/
theorem smoothDDC_comp {F : ComplexModel k → ComplexModel n}
    {ρ : ComplexModel n → ℝ} {U : Set (ComplexModel k)}
    {V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hρ : ContDiffOn ℝ ∞ ρ V)
    (hFV : MapsTo F U V) {z : ComplexModel k} (hz : z ∈ U) :
    smoothDDC (fun y => ρ (F y)) z =
      (smoothDDC ρ (F z)).compContinuousLinearMap (fderiv ℝ F z) :=
  smoothDDC_comp_two hU hV hF
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hFV hz

/-- **Naturality of the Levi form under a holomorphic map.**  This is
`smoothDDC_comp` read off at the complex diagonal; the
second-derivative terms of `F` have already cancelled there. -/
theorem leviForm_comp {F : ComplexModel k → ComplexModel n} {ρ : ComplexModel n → ℝ}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U)
    (hρ : ContDiffOn ℝ ∞ ρ V) (hFV : MapsTo F U V) {z : ComplexModel k} (hz : z ∈ U)
    (v : ComplexModel k) :
    leviForm (fun y => ρ (F y)) z v = leviForm ρ (F z) (fderiv ℝ F z v) := by
  have hFz : DifferentiableAt ℂ F z :=
    ((hF z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hq2 : ContDiffAt ℝ 2 (fun y => ρ (F y)) z := by
    have hqSmooth : ContDiffOn ℝ ∞ (fun y => ρ (F y)) U :=
      hρ.comp (hF.restrict_scalars ℝ) hFV
    exact ((hqSmooth z hz).contDiffAt (hU.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hp2 : ContDiffAt ℝ 2 ρ (F z) :=
    ((hρ (F z) (hFV hz)).contDiffAt (hV.mem_nhds (hFV hz))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnatural := congrArg
    (fun A : (ComplexModel k) [⋀^Fin 2]→L[ℝ] ℝ => A ![v, Complex.I • v])
    (smoothDDC_comp hU hV hF hρ hFV hz)
  have hmapI : fderiv ℝ F z (Complex.I • v) = Complex.I • fderiv ℝ F z v := by
    rw [hFz.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ F z).map_smul Complex.I v
  have hvec : (fun i => fderiv ℝ F z (![v, Complex.I • v] i)) =
      ![fderiv ℝ F z v, fderiv ℝ F z (Complex.I • v)] := by
    ext i
    fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at hnatural
  change smoothDDC (fun y => ρ (F y)) z ![v, Complex.I • v] =
    smoothDDC ρ (F z) (fun i => fderiv ℝ F z (![v, Complex.I • v] i)) at hnatural
  rw [hvec, hmapI, FirstPass.smoothDDC_complexDiagonal_eq_leviForm hq2 v,
    FirstPass.smoothDDC_complexDiagonal_eq_leviForm hp2 (fderiv ℝ F z v)] at hnatural
  exact (div_left_inj₀ Real.pi_ne_zero).mp hnatural

end

end SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
