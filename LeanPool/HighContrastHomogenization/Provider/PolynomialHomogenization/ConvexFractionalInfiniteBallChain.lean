/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexFractionalInfiniteBallChain

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Infinite dyadic ball chains in convex domains
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Dyadic scale decreasing from one to zero. -/
@[expose]
def convexFractionalChainScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- The center at level `n` on the segment from the sandwich center to `x`. -/
@[expose]
def convexFractionalChainCenter (c x : Vec d) (n : ℕ) : Vec d :=
  c + (1 - convexFractionalChainScale n) • (x - c)

/-- The level-`n` ball of the infinite segment chain. -/
@[expose]
def convexFractionalChainBall (c x : Vec d) (rho : ℝ) (n : ℕ) :
    Set (Vec d) :=
  euclideanBallAt (convexFractionalChainCenter c x n)
    (convexFractionalChainScale n * rho)

theorem convexFractionalChainScale_pos (n : ℕ) :
    0 < convexFractionalChainScale n := by
  unfold convexFractionalChainScale
  positivity

theorem convexFractionalChainScale_succ (n : ℕ) :
    convexFractionalChainScale (n + 1) =
      (1 / 2 : ℝ) * convexFractionalChainScale n := by
  unfold convexFractionalChainScale
  rw [pow_succ]
  ring

theorem convexFractionalChainBall_zero (c x : Vec d) (rho : ℝ) :
    convexFractionalChainBall c x rho 0 = euclideanBallAt c rho := by
  ext y
  simp [convexFractionalChainBall, convexFractionalChainCenter,
    convexFractionalChainScale]

/-- Every ball of the infinite segment chain lies in the convex domain. -/
theorem convexFractionalChainBall_subset
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hinner : euclideanBallAt c rho ⊆ U) (hx : x ∈ U) (n : ℕ) :
    convexFractionalChainBall c x rho n ⊆ U := by
  simpa only [convexFractionalChainBall, convexFractionalChainCenter,
    convexFractionalChainScale, convexHardyBallChainCenter,
    convexHardyBallChainRadius, convexHardyBallChainScale_zero] using
      euclideanBallAt_convexHardyBallChainCenter_subset hU.convex hrho
        hinner hx n (0 : Fin (n + 1))

/-- The chain centers converge to the point `x` at the dyadic rate. -/
theorem euclideanDist_convexFractionalChainCenter
    (c x : Vec d) (n : ℕ) :
    euclideanDist x (convexFractionalChainCenter c x n) =
      convexFractionalChainScale n * euclideanDist x c := by
  have hsub : x - convexFractionalChainCenter c x n =
      convexFractionalChainScale n • (x - c) := by
    funext i
    simp only [convexFractionalChainCenter, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  unfold euclideanDist euclideanNorm
  rw [hsub, vecNormSq_smul, Real.sqrt_mul
    (sq_nonneg (convexFractionalChainScale n)), Real.sqrt_sq_eq_abs,
    abs_of_pos (convexFractionalChainScale_pos n)]

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

/-- A member of the level-`n` ball is within the corresponding dyadic
multiple of `Rad + rho` from the endpoint `x`. -/
theorem euclideanDist_lt_scale_mul_add_of_mem_convexFractionalChainBall
    {U : Set (Vec d)} {c x y : Vec d} {rho Rad : ℝ}
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U) (hRad : 0 ≤ Rad)
    (hrho : 0 < rho) {n : ℕ}
    (hy : y ∈ convexFractionalChainBall c x rho n) :
    euclideanDist x y < convexFractionalChainScale n * (Rad + rho) := by
  have hRadpos : 0 < Rad := by
    have hxball := houter hx
    rw [mem_euclideanBallAt_iff] at hxball
    have hne : Rad ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hxball
      exact (not_lt_of_ge (vecNormSq_nonneg _)) hxball
    exact lt_of_le_of_ne hRad (Ne.symm hne)
  have hxc : euclideanDist x c < Rad := by
    have hxball := houter hx
    unfold euclideanDist euclideanNorm
    rw [← Real.sqrt_sq hRadpos.le,
      Real.sqrt_lt_sqrt_iff (vecNormSq_nonneg (x - c))]
    exact hxball
  have hcy : euclideanDist
      (convexFractionalChainCenter c x n) y <
      convexFractionalChainScale n * rho := by
    unfold convexFractionalChainBall at hy
    rw [mem_euclideanBallAt_iff] at hy
    unfold euclideanDist euclideanNorm
    rw [show convexFractionalChainCenter c x n - y =
        -(y - convexFractionalChainCenter c x n) by abel,
      vecNormSq_neg, ← Real.sqrt_sq
        (mul_nonneg (convexFractionalChainScale_pos n).le hrho.le),
      Real.sqrt_lt_sqrt_iff
        (vecNormSq_nonneg (y - convexFractionalChainCenter c x n))]
    exact hy
  calc
    euclideanDist x y ≤
        euclideanDist x (convexFractionalChainCenter c x n) +
          euclideanDist (convexFractionalChainCenter c x n) y :=
      euclideanDist_triangle_le _ _ _
    _ < convexFractionalChainScale n * Rad +
        convexFractionalChainScale n * rho := by
      rw [euclideanDist_convexFractionalChainCenter]
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left hxc.le
          (convexFractionalChainScale_pos n).le) hcy
    _ = convexFractionalChainScale n * (Rad + rho) := by ring

end

end HighContrast
end HCPolySupport
