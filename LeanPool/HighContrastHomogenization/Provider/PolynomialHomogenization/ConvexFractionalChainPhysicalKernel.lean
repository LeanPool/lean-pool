/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalChainPhysicalHead
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.EuclideanBallDistance

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ConvexFractionalChainPhysicalKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical kernel bound for convex fractional chains
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem euclideanDist_triangle_le (x z y : Vec d) :
    euclideanDist x y ≤ euclideanDist x z + euclideanDist z y := by
  calc
    euclideanDist x y = dist (HilbertVec.ofVec x) (HilbertVec.ofVec y) := by
      rw [dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec]
    _ ≤ dist (HilbertVec.ofVec x) (HilbertVec.ofVec z) +
        dist (HilbertVec.ofVec z) (HilbertVec.ofVec y) := dist_triangle _ _ _
    _ = euclideanDist x z + euclideanDist z y := by
      rw [dist_eq_norm, dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec,
        ← euclideanDist_eq_norm_sub_ofVec]

private theorem euclideanDist_lt_two_mul_outerRadius
    {U : Set (Vec d)} {c x y : Vec d} {Rad : ℝ}
    (hRad : 0 < Rad) (houter : U ⊆ euclideanBallAt c Rad)
    (hx : x ∈ U) (hy : y ∈ U) :
    euclideanDist x y < 2 * Rad := by
  have hxc : euclideanDist x c < Rad :=
    (mem_euclideanBallAt_iff_euclideanDist_lt hRad).1 (houter hx)
  have hyc : euclideanDist c y < Rad := by
    rw [euclideanDist_comm]
    exact (mem_euclideanBallAt_iff_euclideanDist_lt hRad).1 (houter hy)
  calc
    euclideanDist x y ≤ euclideanDist x c + euclideanDist c y :=
      euclideanDist_triangle_le _ _ _
    _ < Rad + Rad := add_lt_add hxc hyc
    _ = 2 * Rad := by ring

/-- The growing dyadic weights of all chain balls containing `y` are
controlled by the order-`a` Riesz kernel at `x-y`. -/
theorem tsum_convexFractionalChainBall_weight_le_rieszKernel
    {U : Set (Vec d)} {c x y : Vec d} {rho Rad a : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≠ y) (ha : 0 < a) :
    (∑' n : ℕ, (convexFractionalChainBall c x rho n).indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ a) ^ n)) y) ≤
      ENNReal.ofReal ((2 * Rad) ^ a) *
          ENNReal.ofReal (euclideanDist x y ^ (-a)) +
        ENNReal.ofReal ((Rad + rho) ^ a) *
          ENNReal.ofReal (euclideanDist x y ^ (-a)) *
            ENNReal.ofReal (((2 : ℝ) ^ a) / ((2 : ℝ) ^ a - 1)) := by
  classical
  have hdist : 0 < euclideanDist x y :=
    lt_of_le_of_ne (euclideanDist_nonneg x y)
      (Ne.symm ((euclideanDist_eq_zero_iff).not.mpr hxy))
  have hL : 0 < Rad + rho := add_pos hRad hrho
  simpa only [Set.indicator, Pi.zero_apply] using
    tsum_fractionalChainPhysicalHead_le hdist hL
    (euclideanDist_lt_two_mul_outerRadius hRad houter hx hy) ha
      (fun n => y ∈ convexFractionalChainBall c x rho n) (by
        intro n hn
        simpa only [convexFractionalChainScale] using
          euclideanDist_lt_scale_mul_add_of_mem_convexFractionalChainBall
            houter hx hRad.le hrho hn)

end

end HighContrast
end HCPolySupport
