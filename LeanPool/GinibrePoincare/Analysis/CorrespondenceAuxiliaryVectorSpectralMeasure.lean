/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryVectorSpectralMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralSupportCFC
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Correspondence auxiliary vector spectral measure

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `vectorSpectralMeasure_mass`.
-/

@[expose] public section
open MeasureTheory
open scoped CompactlySupported
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual positive continuous-functional-calculus vector functional,
which supplies the scalar vector spectral measure through Riesz–Markov. -/
def vectorSpectralPositiveFunctional (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (u : H) :
    C_c(spectrum ℝ R, ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ u ((cfcHom hR) f.toContinuousMap u)).re
  map_add' f g := by
    change (inner ℂ u ((cfcHom hR) (f.toContinuousMap+g.toContinuousMap) u)).re = _
    rw [map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    change (inner ℂ u ((cfcHom hR) (c • f.toContinuousMap) u)).re = _
    rw [map_smul, smul_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp
  monotone' f g hfg := by
    have hfc : f.toContinuousMap ≤ g.toContinuousMap := hfg
    have hp := cfcHom_mono hR hfc
    have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hp)
    have h := hpos.re_inner_nonneg_right u
    change 0 ≤ (inner ℂ u (((cfcHom hR) g.toContinuousMap-(cfcHom hR) f.toContinuousMap) u)).re at h
    simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h

/-- A literal scalar vector spectral measure on the compact real spectrum
of a bounded self-adjoint operator; no measure is supplied as a hypothesis. -/
def vectorSpectralMeasure (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (u : H) :
    Measure (spectrum ℝ R) :=
  RealRMK.rieszMeasure (vectorSpectralPositiveFunctional R hR u)

/-- The defining spectral-calculus integral identity for every continuous
compactly supported spectral test. -/
theorem integral_vectorSpectralMeasure (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (u : H) (f : C_c(spectrum ℝ R, ℝ)) :
    (∫ x, f x ∂vectorSpectralMeasure R hR u) =
      (inner ℂ u ((cfcHom hR) f.toContinuousMap u)).re :=
  RealRMK.integral_rieszMeasure (vectorSpectralPositiveFunctional R hR u) f

instance vectorSpectralMeasure_finite (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (u : H) :
    IsFiniteMeasure (vectorSpectralMeasure R hR u) := by
  unfold vectorSpectralMeasure
  infer_instance

/-- Total mass of the actual scalar spectral measure is exactly the vector's
squared Hilbert norm. -/
theorem vectorSpectralMeasure_mass (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (u : H) : (vectorSpectralMeasure R hR u) Set.univ = ENNReal.ofReal (‖u‖^2) := by
  let oneTest : C_c(spectrum ℝ R, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  have h := integral_vectorSpectralMeasure R hR u oneTest
  have hone : oneTest.toContinuousMap = 1 := rfl
  rw [hone, map_one] at h
  simp only [one_apply_eq_self] at h
  have hre : (inner ℂ u u).re = ‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  rw [hre] at h
  change (∫ _ : spectrum ℝ R, (1 : ℝ) ∂vectorSpectralMeasure R hR u) = ‖u‖^2 at h
  simp only [integral_const,
    smul_eq_mul, mul_one, measureReal_def] at h
  rw [← h, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

end
end GinibrePoincare
