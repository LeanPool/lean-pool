/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolution

/-!
# Pointwise bound for complex Schwartz mollification

The convolution of the fixed Schwartz kernel with an L² Schwartz
velocity is bounded at each spatial point by the L² Hölder estimate.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Complex Schwartz mollification obeys the L²-by-L² pointwise
convolution bound. -/
theorem regularisedSchwartzMollify_enorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    ‖regularisedSchwartzMollify ρ ε hε ψ x‖ₑ ≤
      ‖(ContinuousLinearMap.lsmul ℂ ℂ :
        ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3)‖ₑ *
        eLpNorm (fun y : L2Vec3 =>
          ((regMollifierKernel ρ ε hε y : ℝ) : ℂ)) 2 volume *
        eLpNorm (ψ : L2Vec3 → ComplexVec3) 2 volume := by
  rw [regularisedSchwartzMollify_apply]
  exact MeasureTheory.enorm_convolution_le
    (L := (ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3))
    (p := (2 : ℝ≥0∞)) (q := 2)
    (regularisedComplexMollifierSchwartz ρ ε hε).continuous.aestronglyMeasurable
    ψ.continuous.aestronglyMeasurable x

/-- Complex Schwartz mollification has pointwise bound with the exact
L² kernel factor, since scalar multiplication has bilinear norm one. -/
theorem regularisedSchwartzMollify_enorm_le_kernel
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    ‖regularisedSchwartzMollify ρ ε hε ψ x‖ₑ ≤
      eLpNorm (fun y : L2Vec3 =>
        ((regMollifierKernel ρ ε hε y : ℝ) : ℂ)) 2 volume *
        eLpNorm (ψ : L2Vec3 → ComplexVec3) 2 volume := by
  have hL : ‖(ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3)‖ₑ ≤ 1 := by
    apply ContinuousLinearMap.opENorm_le_iff.mpr
    intro c
    have hc : ‖(ContinuousLinearMap.lsmul ℂ ℂ :
        ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3) c‖ₑ ≤ ‖c‖ₑ := by
      apply ContinuousLinearMap.opENorm_le_bound
      intro z
      change ‖c • z‖ₑ ≤ _
      exact enorm_smul_le
    rw [one_mul]
    exact hc
  calc
    ‖regularisedSchwartzMollify ρ ε hε ψ x‖ₑ ≤
        ‖(ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3)‖ₑ *
          eLpNorm (fun y : L2Vec3 =>
            ((regMollifierKernel ρ ε hε y : ℝ) : ℂ)) 2 volume *
          eLpNorm (ψ : L2Vec3 → ComplexVec3) 2 volume :=
      regularisedSchwartzMollify_enorm_le ρ ε hε ψ x
    _ ≤ 1 * eLpNorm (fun y : L2Vec3 =>
          ((regMollifierKernel ρ ε hε y : ℝ) : ℂ)) 2 volume *
          eLpNorm (ψ : L2Vec3 → ComplexVec3) 2 volume := by
            gcongr
    _ = _ := by simp

/-- One finite constant, fixed by the mollifier and scale, bounds
complex Schwartz mollification pointwise by the input L² norm. -/
theorem regularisedSchwartzMollify_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3),
        ‖regularisedSchwartzMollify ρ ε hε ψ x‖ ≤
          C * ‖ψ.toLp 2‖ := by
  let k := regularisedComplexMollifierSchwartz ρ ε hε
  let C : ℝ := (eLpNorm k (2 : ℝ≥0∞) volume).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  refine ⟨C, hC, ?_⟩
  intro ψ x
  have hBound := regularisedSchwartzMollify_enorm_le_kernel
    ρ ε hε ψ x
  have hFinite : (eLpNorm k (2 : ℝ≥0∞) volume *
      eLpNorm ψ (2 : ℝ≥0∞) volume) ≠ ∞ :=
    (ENNReal.mul_lt_top (k.memLp 2 volume).eLpNorm_lt_top
      (ψ.memLp 2 volume).eLpNorm_lt_top).ne
  have hReal := ENNReal.toReal_mono hFinite hBound
  simpa only [toReal_enorm, ENNReal.toReal_mul,
    SchwartzMap.norm_toLp, C, k,
    regularisedComplexMollifierSchwartz_apply] using hReal

end CKN.Leray

end
