/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern
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

/-- The complete normalized two-form, not just its diagonal values, commutes
with a smooth holomorphic map between open sets. -/
theorem smoothDDC_comp {F : ComplexModel k → ComplexModel n}
    {ρ : ComplexModel n → ℝ} {U : Set (ComplexModel k)}
    {V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F U) (hρ : ContDiffOn ℝ ∞ ρ V)
    (hFV : MapsTo F U V) {z : ComplexModel k} (hz : z ∈ U) :
    smoothDDC (fun y => ρ (F y)) z =
      (smoothDDC ρ (F z)).compContinuousLinearMap (fderiv ℝ F z) := by
  have heq : smoothDc (fun y => ρ (F y)) =ᶠ[𝓝 z]
      (fun y => (smoothDc ρ (F y)).compContinuousLinearMap (fderiv ℝ F y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact smoothDc_comp
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (((hρ (F y) (hFV hy)).contDiffAt (hV.mem_nhds (hFV hy))).differentiableAt
        (by simp))
  apply heq.extDeriv_eq.trans
  exact extDeriv_pullback
    ((((smoothDc_contDiffOn hV hρ) (F z) (hFV hz)).contDiffAt
      (hV.mem_nhds (hFV hz))).differentiableAt (by simp))
    (((hF.restrict_scalars ℝ) z hz).contDiffAt (hU.mem_nhds hz))
    (by simp)

end

end SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
