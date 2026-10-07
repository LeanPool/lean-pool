/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierGeneral
public import Mathlib.Analysis.Fourier.Convolution

/-!
# The mollifier kernel as a Schwartz field

The fixed smooth compactly supported mollifier defines a complex
Schwartz scalar field on the Fourier spatial carrier.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

theorem regularisedComplexMollifier_smooth
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : L2Vec3 =>
        ((regMollifierKernel ρ ε hε x : ℝ) : ℂ)) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => ε⁻¹ • y) := by
    fun_prop
  have hreal : ContDiff ℝ (⊤ : ℕ∞)
      (regMollifierKernel ρ ε hε) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact contDiff_const.mul (ρ.smooth.comp hscale)
  exact Complex.ofRealCLM.contDiff.comp hreal

theorem regularisedComplexMollifier_compact
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport
      (fun x : L2Vec3 =>
        ((regMollifierKernel ρ ε hε x : ℝ) : ℂ)) := by
  have hreal : HasCompactSupport
      (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have hcomp := ρ.compact.comp_homeomorph
      (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    exact hcomp.mul_left
  change HasCompactSupport
    (Complex.ofRealCLM ∘ regMollifierKernel ρ ε hε)
  exact hreal.comp_left (by simp)

/-- The real mollifier kernel, embedded in the complex scalars, is a
Schwartz field. -/
@[expose]
def regularisedComplexMollifierSchwartz
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    𝓢(L2Vec3, ℂ) :=
  (regularisedComplexMollifier_compact ρ ε hε).toSchwartzMap
    (regularisedComplexMollifier_smooth ρ ε hε)

/-- The Schwartz kernel agrees pointwise with the complexified
regularized mollifier. -/
theorem regularisedComplexMollifierSchwartz_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (x : L2Vec3) :
    regularisedComplexMollifierSchwartz ρ ε hε x =
      ((regMollifierKernel ρ ε hε x : ℝ) : ℂ) := rfl

end CKN.Leray

end
