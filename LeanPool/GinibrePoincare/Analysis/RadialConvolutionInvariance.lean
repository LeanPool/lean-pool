/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialConvolutionInvariance.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialGaussianOrthogonality
public import LeanPool.GinibrePoincare.Analysis.GinibreSpatialCutoffs
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Radial and symmetric convolution under Lebesgue measure

Independent coordinate phases preserve Lebesgue measure. Radial kernels and
radial values therefore have radial convolutions; permutation invariance is
preserved as well. Concrete spatial-radius cutoffs provide such kernels.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace GinibrePoincare
noncomputable section

/-- Coordinate unit phases as a measurable equivalence. -/
def coordinatePhaseLebesgueEquiv (n : ℕ) (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    Configuration n ≃ᵐ Configuration n :=
  MeasurableEquiv.piCongrRight fun i => complexMulMeasurableEquiv (u i) (by
    intro he; have ht := hu i; rw [he, norm_zero] at ht; norm_num at ht)

/-- Independent unit rotations preserve actual configuration Lebesgue measure. -/
theorem measurePreserving_coordinatePhase_volume (n : ℕ)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    MeasurePreserving (coordinatePhaseLebesgueEquiv n u hu)
      (volume : Measure (Configuration n)) volume := by
  exact measurePreserving_pi _ _ (fun i => measurePreserving_complex_mul_of_norm_one (u i) (hu i))

/-- A function of individual squared radii is invariant under independent phases. -/
theorem radial_coordinatePhase {n : ℕ} {f : Configuration n → ℝ}
    (hf : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) (z : Configuration n) :
    f (coordinatePhase u z) = f z := by
  obtain ⟨F, hF⟩ := hf
  rw [hF, hF]
  congr 1
  funext i
  simp [coordinatePhase, ← Complex.sq_norm, hu i]

/-- Phase invariance gives an actual squared-radius witness, including zero coordinates. -/
theorem radial_of_coordinatePhase {n : ℕ} {f : Configuration n → ℝ}
    (hf : ∀ u : Fin n → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z, f (coordinatePhase u z) = f z) :
    ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)) := by
  classical
  refine ⟨fun r => f (fun i => (Real.sqrt (r i) : ℂ)), ?_⟩
  intro z
  choose u hu he using (fun i : Fin n => Complex.exists_norm_mul_eq_self (z i))
  have hz : coordinatePhase u (fun i => (Real.sqrt (Complex.normSq (z i)) : ℂ)) = z := by
    funext i
    change u i * (Real.sqrt (Complex.normSq (z i)) : ℂ) = z i
    rw [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]
    exact he i
  exact (congrArg f hz).symm.trans (hf u hu _)

/-- Convolution preserves the individual squared-radius property. -/
theorem radial_convolution {n : ℕ} (a f : Configuration n → ℝ)
    (ha : ∃ A : (Fin n → ℝ) → ℝ, ∀ z, a z = A (fun i => Complex.normSq (z i)))
    (hf : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ F : (Fin n → ℝ) → ℝ, ∀ z,
      (a ⋆[lsmul ℝ ℝ, volume] f) z = F (fun i => Complex.normSq (z i)) := by
  apply radial_of_coordinatePhase
  intro u hu z
  rw [convolution_lsmul, convolution_lsmul]
  simp only [smul_eq_mul]
  have hm := (measurePreserving_coordinatePhase_volume n u hu).integral_comp'
    (fun y => a y * f (coordinatePhase u z - y))
  calc
    _ = ∫ y, a (coordinatePhase u y) * f (coordinatePhase u z - coordinatePhase u y) := hm.symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      dsimp only
      have he : coordinatePhase u z - coordinatePhase u y = coordinatePhase u (z - y) := by
        funext i
        exact (mul_sub (u i) (z i) (y i)).symm
      rw [he, radial_coordinatePhase ha u hu y, radial_coordinatePhase hf u hu (z - y)]

/-- Convolution preserves permutation symmetry. -/
theorem symmetric_convolution {n : ℕ} (a f : Configuration n → ℝ)
    (ha : IsSymmetric a) (hf : IsSymmetric f) :
    IsSymmetric (a ⋆[lsmul ℝ ℝ, volume] f) := by
  intro σ z
  rw [convolution_lsmul, convolution_lsmul]
  simp only [smul_eq_mul]
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) σ.symm
  change MeasurePreserving (permutationMeasurableEquiv σ) volume volume at hp
  have hm := hp.integral_comp' (fun y => a y * f (permute σ z - y))
  calc
    _ = ∫ y, a (permute σ y) * f (permute σ z - permute σ y) := by
      simpa only [permutationMeasurableEquiv_apply] using hm.symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change a (permute σ y) * f (permute σ (z - y)) = a y * f (z - y)
      rw [ha σ y, hf σ (z - y)]

/-- Concrete radius-cutoff convolution of a compact radial symmetric L² value
is in the original smooth radial Sobolev core. -/
theorem ginibreSpatialCutoff_convolution_core (n m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    IsRadialSobolevCore (ginibreSpatialCutoff n m ⋆[lsmul ℝ ℝ, volume] f) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (ginibreSpatialCutoff_compact n m).contDiff_convolution_left _
      (ginibreSpatialCutoff_smooth n m) (hf.locallyIntegrable (by norm_num))
  · exact (ginibreSpatialCutoff_compact n m).convolution _ hc
  · exact symmetric_convolution _ _ (ginibreSpatialCutoff_symmetric n m) hs
  · exact radial_convolution _ _ (ginibreSpatialCutoff_radial n m) hr

end
end GinibrePoincare
