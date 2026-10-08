/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyLocalLayer
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyBallChain

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Ball chains in convex domains

A concentric ball sandwich supplies a canonical chain of interior balls from
any point of the domain to the fixed inner ball.  The centers lie on the
segment from the point to the sandwich center, while the radii double at each
step.  The initial radius can be chosen between a prescribed positive scale
and twice that scale.

The explicit indexing and center-distance bounds are designed for telescoping
estimates between averages over successive balls.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The geometric scale at the `i`-th member of a chain of length `N`. -/
@[expose]
def convexHardyBallChainScale (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ N

/-- The center at the `i`-th member of the segment chain from `x` to `c`. -/
@[expose]
def convexHardyBallChainCenter (c x : Vec d) (N : ℕ)
    (i : Fin (N + 1)) : Vec d :=
  c + (1 - convexHardyBallChainScale N i) • (x - c)

/-- The radius at the `i`-th member of a chain with terminal radius `rho`. -/
@[expose]
def convexHardyBallChainRadius (rho : ℝ) (N : ℕ)
    (i : Fin (N + 1)) : ℝ :=
  convexHardyBallChainScale N i * rho

/-- Finite geometric ball-chain data at an initial scale `r`. -/
structure ConvexHardyBallChain (U : Set (Vec d)) (x : Vec d)
    (rho Rad r : ℝ) where
  /-- Terminal center of the geometric ball chain. -/
  center : Vec d
  /-- Number of successive radius doublings, giving a chain of one more ball. -/
  length : ℕ
  initial_radius_lower :
    r ≤ convexHardyBallChainRadius rho length 0
  initial_radius_upper :
    convexHardyBallChainRadius rho length 0 < 2 * r
  balls_subset : ∀ i : Fin (length + 1),
    euclideanBallAt
        (convexHardyBallChainCenter center x length i)
        (convexHardyBallChainRadius rho length i) ⊆ U
  terminal_center :
    convexHardyBallChainCenter center x length (Fin.last length) = center
  terminal_radius :
    convexHardyBallChainRadius rho length (Fin.last length) = rho
  radius_succ : ∀ i : Fin length,
    convexHardyBallChainRadius rho length i.succ =
      2 * convexHardyBallChainRadius rho length i.castSucc
  initial_center_dist :
    dist x (convexHardyBallChainCenter center x length 0) <
      (Rad / rho) * convexHardyBallChainRadius rho length 0
  center_dist_succ : ∀ i : Fin length,
    dist (convexHardyBallChainCenter center x length i.castSucc)
        (convexHardyBallChainCenter center x length i.succ) <
      (Rad / rho) *
        convexHardyBallChainRadius rho length i.castSucc

theorem convexHardyBallChainScale_pos (N : ℕ) (i : Fin (N + 1)) :
    0 < convexHardyBallChainScale N i := by
  unfold convexHardyBallChainScale
  positivity

theorem convexHardyBallChainScale_le_one (N : ℕ) (i : Fin (N + 1)) :
    convexHardyBallChainScale N i ≤ 1 := by
  rw [convexHardyBallChainScale, div_le_one (by positivity)]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.le_of_lt_succ i.isLt)

theorem convexHardyBallChainScale_zero (N : ℕ) :
    convexHardyBallChainScale N 0 = (1 / 2 : ℝ) ^ N := by
  simp [convexHardyBallChainScale]

theorem convexHardyBallChainScale_last (N : ℕ) :
    convexHardyBallChainScale N (Fin.last N) = 1 := by
  simp [convexHardyBallChainScale]

theorem convexHardyBallChainScale_succ (N : ℕ) (i : Fin N) :
    convexHardyBallChainScale N i.succ =
      2 * convexHardyBallChainScale N i.castSucc := by
  simp only [convexHardyBallChainScale, Fin.val_succ, Fin.val_castSucc,
    pow_succ]
  ring

theorem convexHardyBallChainCenter_last (c x : Vec d) (N : ℕ) :
    convexHardyBallChainCenter c x N (Fin.last N) = c := by
  simp [convexHardyBallChainCenter, convexHardyBallChainScale_last]

theorem convexHardyBallChainRadius_last (rho : ℝ) (N : ℕ) :
    convexHardyBallChainRadius rho N (Fin.last N) = rho := by
  simp [convexHardyBallChainRadius, convexHardyBallChainScale_last]

theorem convexHardyBallChainRadius_succ (rho : ℝ) (N : ℕ)
    (i : Fin N) :
    convexHardyBallChainRadius rho N i.succ =
      2 * convexHardyBallChainRadius rho N i.castSucc := by
  rw [convexHardyBallChainRadius, convexHardyBallChainRadius,
    convexHardyBallChainScale_succ]
  ring

private theorem convexHardyBallChainLambda_mem_Ico (N : ℕ)
    (i : Fin (N + 1)) :
    1 - convexHardyBallChainScale N i ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (convexHardyBallChainScale_le_one N i)
  · exact sub_lt_self 1 (convexHardyBallChainScale_pos N i)

/-- Every member of the geometric chain is contained in the convex domain. -/
theorem euclideanBallAt_convexHardyBallChainCenter_subset
    {U : Set (Vec d)} (hconv : Convex ℝ U) {c x : Vec d} {rho : ℝ}
    (hrho : 0 < rho) (hinner : euclideanBallAt c rho ⊆ U)
    (hx : x ∈ U) (N : ℕ) (i : Fin (N + 1)) :
    euclideanBallAt (convexHardyBallChainCenter c x N i)
        (convexHardyBallChainRadius rho N i) ⊆ U := by
  have h := euclideanBallAt_dilate_subset_of_convex hconv hrho hinner
    (convexHardyBallChainLambda_mem_Ico N i) hx
  simpa [convexHardyBallChainCenter, convexHardyBallChainRadius] using h

theorem dist_convexHardyBallChainCenter_succ (c x : Vec d) (N : ℕ)
    (i : Fin N) :
    dist (convexHardyBallChainCenter c x N i.castSucc)
        (convexHardyBallChainCenter c x N i.succ) =
      convexHardyBallChainScale N i.castSucc * dist x c := by
  have hscale := convexHardyBallChainScale_succ N i
  have hsub :
      convexHardyBallChainCenter c x N i.castSucc -
          convexHardyBallChainCenter c x N i.succ =
        convexHardyBallChainScale N i.castSucc • (x - c) := by
    funext j
    simp only [convexHardyBallChainCenter, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hscale]
    ring
  calc
    dist (convexHardyBallChainCenter c x N i.castSucc)
        (convexHardyBallChainCenter c x N i.succ) =
        ‖convexHardyBallChainCenter c x N i.castSucc -
          convexHardyBallChainCenter c x N i.succ‖ := dist_eq_norm _ _
    _ = ‖convexHardyBallChainScale N i.castSucc • (x - c)‖ := by rw [hsub]
    _ = |convexHardyBallChainScale N i.castSucc| * ‖x - c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = convexHardyBallChainScale N i.castSucc * ‖x - c‖ := by
      rw [abs_of_pos (convexHardyBallChainScale_pos N i.castSucc)]
    _ = convexHardyBallChainScale N i.castSucc * dist x c := by
      rw [dist_eq_norm]

theorem dist_convexHardyBallChainCenter_zero (c x : Vec d) (N : ℕ) :
    dist x (convexHardyBallChainCenter c x N 0) =
      convexHardyBallChainScale N 0 * dist x c := by
  have hsub :
      x - convexHardyBallChainCenter c x N 0 =
        convexHardyBallChainScale N 0 • (x - c) := by
    funext j
    simp only [convexHardyBallChainCenter, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  calc
    dist x (convexHardyBallChainCenter c x N 0) =
        ‖x - convexHardyBallChainCenter c x N 0‖ := dist_eq_norm _ _
    _ = ‖convexHardyBallChainScale N 0 • (x - c)‖ := by rw [hsub]
    _ = |convexHardyBallChainScale N 0| * ‖x - c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = convexHardyBallChainScale N 0 * ‖x - c‖ := by
      rw [abs_of_pos (convexHardyBallChainScale_pos N 0)]
    _ = convexHardyBallChainScale N 0 * dist x c := by rw [dist_eq_norm]

end

end HighContrast
end HCPolySupport
