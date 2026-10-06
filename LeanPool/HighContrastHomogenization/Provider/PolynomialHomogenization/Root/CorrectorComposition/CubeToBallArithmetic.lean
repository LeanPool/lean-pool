/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PrintOrderGaugeRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CubeToBallArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cube-to-ball packaging: the decay conversion

The exact-gauge simultaneous-slope row decays in the **triadic generation gap**,
`3 ^ (-η · (m - q))`.  The large-scale C¹ slope approximation clause terminal decays in the
**radius ratio**,
`(r / R) ^ η`.  No declaration converts one to
the other (the two existing generation-gap identities,
`HCPolySupport.HighContrast.Quenched.triadic_gap_rpow_eq` and
`triadic_weight_inv_eq_gap_rpow`, are `private` in
`HCPoly.Provider.Quenched.CoupledMixingScaleDecay`, and both are
single-endpoint).

This module supplies the conversion, order-generic and with an explicit
law-free constant.  It is the arithmetic half of the packaging; the geometric
half is the sandwich

* `ball r ⊆ openCubeSet (originCube d q)` with `3 ^ q ≤ K₁ · r`, and
* `openCubeSet (originCube d m) ⊆ ball R` with `K₂ · R ≤ 3 ^ m`,

for which the inclusions
`euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration` and
`openCubeSet_originCube_subset_scaleMatchedEuclideanBall` and the volume-ratio monotonicity
`weightedGradNorm_mono_set_le_volumeRatio` are the
ingredients.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open Real

noncomputable section

/-- The generation gap, rewritten as a scale ratio. -/
theorem triadicGap_rpow_eq {q m : ℕ} (hqm : q ≤ m) (eta : ℝ) :
    (3 : ℝ) ^ (-eta * ((m - q : ℕ) : ℝ)) =
      ((3 : ℝ) ^ q / (3 : ℝ) ^ m) ^ eta := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h3' : (0 : ℝ) < 3 := by norm_num
  have hcast : ((m - q : ℕ) : ℝ) = (m : ℝ) - (q : ℝ) := by
    exact Nat.cast_sub hqm
  have harg : -eta * ((m - q : ℕ) : ℝ) = ((q : ℝ) - (m : ℝ)) * eta := by
    rw [hcast]; ring
  have hsplit : (3 : ℝ) ^ ((q : ℝ) - (m : ℝ)) = (3 : ℝ) ^ q / (3 : ℝ) ^ m := by
    rw [Real.rpow_sub h3', Real.rpow_natCast, Real.rpow_natCast]
  rw [harg, Real.rpow_mul h3, hsplit]

/-- **The decay conversion.**  A generation-gap decay becomes a radius-ratio
decay, at the explicit law-free cost `(K₁ / K₂) ^ η`. -/
theorem triadicGap_le_radiusRatio {q m : ℕ} (hqm : q ≤ m)
    {eta K₁ K₂ r R : ℝ} (heta : 0 ≤ eta)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hr : 0 < r) (hR : 0 < R)
    (hq : (3 : ℝ) ^ q ≤ K₁ * r) (hm : K₂ * R ≤ (3 : ℝ) ^ m) :
    (3 : ℝ) ^ (-eta * ((m - q : ℕ) : ℝ)) ≤
      (K₁ / K₂) ^ eta * (r / R) ^ eta := by
  have hmpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hratio : (3 : ℝ) ^ q / (3 : ℝ) ^ m ≤ K₁ / K₂ * (r / R) := by
    rw [div_le_iff₀ hmpos]
    have hstep : K₁ / K₂ * (r / R) * (K₂ * R) = K₁ * r := by
      field_simp
    calc (3 : ℝ) ^ q ≤ K₁ * r := hq
      _ = K₁ / K₂ * (r / R) * (K₂ * R) := hstep.symm
      _ ≤ K₁ / K₂ * (r / R) * (3 : ℝ) ^ m := by
          have hpos : (0 : ℝ) ≤ K₁ / K₂ * (r / R) := by positivity
          exact mul_le_mul_of_nonneg_left hm hpos
  rw [triadicGap_rpow_eq hqm eta,
    ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) hratio heta

end

end CorrectorComposition
end HighContrast
end HCPolySupport
