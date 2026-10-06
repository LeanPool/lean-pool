/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube

/-!
# High-contrast homogenization: Provider.Regularity.AffineFlatnessPrep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine-candidate error algebra on Euclidean cubes

The normalized distance below is the scale-invariant `L²` quantity used in
affine approximation.  The main lemmas transfer one affine candidate across a
comparison estimate.  They are metric-algebra statements and do not assert
constant-coefficient harmonic decay.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Scale-normalized `L²` distance between two scalar fields on a triadic
cube. -/
@[expose]
def normalizedCubeL2Distance {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) : ℝ :=
  cubeBesovScaleWeight (1 : ℝ) Q *
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ f x - g x)

/-- Scale-normalized `L²` error relative to the affine candidate
`x ↦ c + e · x`. -/
@[expose]
def normalizedAffineCandidateError {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) (c : ℝ) (e : Vec d) : ℝ :=
  normalizedCubeL2Distance Q f (fun x ↦ c + vecDot e x)

/-- The normalized cube distance is nonnegative. -/
theorem normalizedCubeL2Distance_nonneg {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) :
    0 ≤ normalizedCubeL2Distance Q f g :=
  mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q)
    (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x ↦ f x - g x))

/-- Every normalized affine-candidate error is nonnegative. -/
theorem normalizedAffineCandidateError_nonneg {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) (c : ℝ) (e : Vec d) :
    0 ≤ normalizedAffineCandidateError Q f c e :=
  normalizedCubeL2Distance_nonneg Q f _

/-- Moving an affine candidate across an intermediate comparison function
costs at most the normalized distance to that function. -/
theorem normalizedAffineCandidateError_le_distance_add {d : ℕ}
    (Q : TriadicCube d) (u h : Vec d → ℝ) (c : ℝ) (e : Vec d)
    (hcomparison : MemLp (fun x ↦ u x - h x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hcandidate : MemLp (fun x ↦ h x - (c + vecDot e x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    normalizedAffineCandidateError Q u c e ≤
      normalizedCubeL2Distance Q u h +
        normalizedAffineCandidateError Q h c e := by
  have htriangle :=
    cubeLpNorm_add_le Q (2 : ℝ≥0∞)
      (fun x ↦ u x - h x) (fun x ↦ h x - (c + vecDot e x))
      hcomparison hcandidate (by norm_num)
  have hweight : 0 ≤ cubeBesovScaleWeight (1 : ℝ) Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  calc
    normalizedAffineCandidateError Q u c e =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ (u x - h x) + (h x - (c + vecDot e x))) := by
      unfold normalizedAffineCandidateError normalizedCubeL2Distance
      congr 2
      funext x
      ring
    _ ≤ cubeBesovScaleWeight (1 : ℝ) Q *
        (cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ u x - h x) +
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ h x - (c + vecDot e x))) :=
      mul_le_mul_of_nonneg_left htriangle hweight
    _ = normalizedCubeL2Distance Q u h +
        normalizedAffineCandidateError Q h c e := by
      rw [mul_add]
      rfl

end

end HighContrast
end HCPolySupport
