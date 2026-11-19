/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeakTests.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebLocalL2
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
/-!
# Correspondence Brascamp Lieb weak tests

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_weak_test_C1`.
-/

@[expose] public section
open MeasureTheory Measure Filter
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Ordinary distributional derivatives are tested against actual Lebesgue
measure. The weighted L² assumptions supply local Lebesgue integrability. -/
def CorrespondenceBrascampLiebHasWeakDerivative (u G : E → ℝ) (v : E) : Prop :=
  ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    (∫ x, θ x * G x) = -(∫ x, fderiv ℝ θ x v * u x)

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_weak_localization
    (W u G : E → ℝ) (v : E) (hW : Continuous W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : CorrespondenceBrascampLiebLocallyL2 G)
    (hw : CorrespondenceBrascampLiebHasWeakDerivative u G v)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ U J : Lp ℝ 2 (volume : Measure E),
      (U : E → ℝ) =ᵐ[volume] (fun x => χ x*u x) ∧
      (J : E → ℝ) =ᵐ[volume] (fun x => χ x*G x+fderiv ℝ χ x v*u x) ∧
      ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ x, θ x*J x) = -(∫ x, fderiv ℝ θ x v*U x) := by
  let ρ := bakryEmeryGibbsWeight W
  have hρ : Continuous ρ := Real.continuous_exp.comp hW.neg
  have hp : ∀x, 0<ρ x := fun _ => Real.exp_pos _
  let d : E → ℝ := fun x => fderiv ℝ χ x v
  have hd : Continuous d := (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ v
  have hU := correspondenceWeightedElliptic_compact_value_memLp ρ hρ hp u χ hu hχ.continuous hc
  have hJG := correspondenceBrascampLieb_localL2_compact_multiplier G χ hG hχ.continuous hc
  have hJU := correspondenceWeightedElliptic_compact_value_memLp ρ hρ hp u d hu hd hdc
  have hJ := hJG.add hJU
  refine ⟨hU.toLp _, hJ.toLp _, hU.coeFn_toLp, hJ.coeFn_toLp,?_⟩
  intro θ hθ hθc
  have hul := correspondenceWeightedElliptic_locallyIntegrable ρ hρ hp u hu
  have hGl := correspondenceBrascampLieb_localL2_locallyIntegrable G hG
  have hDθ : Continuous (fun x => fderiv ℝ θ x v) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun x => θ x*χ x*G x) := by
    simpa only [smul_eq_mul, Pi.mul_apply, mul_comm] using
      hGl.integrable_smul_right_of_hasCompactSupport (hθ.continuous.mul hχ.continuous)
        (hθc.mul_right)
  have hi2 : Integrable (fun x => θ x*d x*u x) := by
    simpa only [smul_eq_mul, Pi.mul_apply, mul_comm] using
      hul.integrable_smul_right_of_hasCompactSupport (hθ.continuous.mul hd) (hθc.mul_right)
  have hi3 : Integrable (fun x => χ x*fderiv ℝ θ x v*u x) := by
    simpa only [smul_eq_mul, Pi.mul_apply, mul_comm] using
      hul.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hDθ) (hc.mul_right)
  have he := hw (χ*θ) (hχ.mul hθ) (hc.mul_right)
  have hder (x : E) : fderiv ℝ (χ*θ) x v = d x*θ x+χ x*fderiv ℝ θ x v := by
    rw [fderiv_mul (hχ.differentiable (by simp) x) (hθ.differentiable (by simp) x)]
    simp [d, mul_comm, add_comm]
  have he' : (∫ x, θ x*χ x*G x) =
      -(∫ x, θ x*d x*u x) -(∫ x, χ x*fderiv ℝ θ x v*u x) := by
    have hl : (∫ x, (χ*θ) x*G x) = ∫ x, θ x*χ x*G x := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => by simp only [Pi.mul_apply]; ring
    have hr : (∫ x, fderiv ℝ (χ*θ) x v*u x) =
      (∫ x, θ x*d x*u x)+(∫ x, χ x*fderiv ℝ θ x v*u x) := by
      simp_rw [hder]
      have heq : (fun x => (d x*θ x+χ x*fderiv ℝ θ x v)*u x) =
          (fun x => θ x*d x*u x)+(fun x => χ x*fderiv ℝ θ x v*u x) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact integral_add hi2 hi3
    rw [hl, hr] at he
    linarith
  have hl : (∫ x, θ x*(hJ.toLp _ : E → ℝ) x) =
      (∫ x, θ x*χ x*G x)+(∫ x, θ x*d x*u x) := by
    have heq : (fun x => θ x*(χ x*G x+d x*u x)) =
        (fun x => θ x*χ x*G x)+(fun x => θ x*d x*u x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    calc
      _ = ∫ x, θ x*(χ x*G x+d x*u x) := by
        apply integral_congr_ae
        filter_upwards [hJ.coeFn_toLp] with x hx
        rw [hx]
        rfl
      _ = _ := by rw [heq]; exact integral_add hi1 hi2
  have hr : (∫ x, fderiv ℝ θ x v*(hU.toLp _ : E → ℝ) x) =
      ∫ x, χ x*fderiv ℝ θ x v*u x := by
    apply integral_congr_ae
    filter_upwards [hU.coeFn_toLp] with x hx
    rw [hx]
    ring
  rw [hl, hr]
  linarith

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_weak_test_C1
    (W u G : E → ℝ) (v : E) (hW : Continuous W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : CorrespondenceBrascampLiebLocallyL2 G)
    (hw : CorrespondenceBrascampLiebHasWeakDerivative u G v)
    (θ : E → ℝ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ x, θ x*G x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff (tsupport θ) hc
  obtain ⟨U, J, hU, hJ, hwJ⟩ := correspondenceBrascampLieb_weak_localization W u G v hW
    hu hG hw χ hχ hχc
  have he := correspondenceWeightedElliptic_weak_test_C1 U J v hwJ θ hθ hc
  have hl : (∫ x, θ x*J x) = ∫ x, θ x*G x := by
    apply integral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
    by_cases hs : x ∈ tsupport θ
    · have hx1 : χ x = 1 := (hχone x hs).eq_of_nhds
      have hxD : fderiv ℝ χ x v = 0 := by
        rw [(hχone x hs).fderiv_eq]
        simp
      rw [hx1, hxD]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]
  have hr : (∫ x, fderiv ℝ θ x v*U x) = ∫ x, fderiv ℝ θ x v*u x := by
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx]
    by_cases hs : x ∈ tsupport θ
    · have hx1 : χ x = 1 := (hχone x hs).eq_of_nhds
      rw [hx1]
      ring
    · have hzero : fderiv ℝ θ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hs
      simp [hzero]
  rwa [hl, hr] at he

end
end GinibrePoincare
