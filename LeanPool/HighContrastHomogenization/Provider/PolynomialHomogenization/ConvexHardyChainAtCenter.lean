/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyChainAtCenter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Convex Hardy chains at a fixed sandwich center

The ball-sandwich data provide one distinguished center.  All chains used in
the Whitney aggregation can be chosen with that same center while retaining
the common scale bounds from the abstract chain construction.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

private theorem convexHardyBallChainCenter_dist_lt_at_center
    {U : Set (Vec d)} {c x : Vec d} {rho Rad : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U)
    (N : ℕ) (i : Fin (N + 1)) :
    convexHardyBallChainScale N i * dist x c <
      (Rad / rho) * convexHardyBallChainRadius rho N i := by
  have hxcMetric : x ∈ Metric.ball c Rad :=
    euclideanBallAt_subset_metricBall c hRad (houter hx)
  have hxc : dist x c < Rad := Metric.mem_ball.mp hxcMetric
  calc
    convexHardyBallChainScale N i * dist x c <
        convexHardyBallChainScale N i * Rad :=
      mul_lt_mul_of_pos_left hxc (convexHardyBallChainScale_pos N i)
    _ = (Rad / rho) * convexHardyBallChainRadius rho N i := by
      unfold convexHardyBallChainRadius
      field_simp [hrho.ne']

/-- Prescribed initial-radius bounds construct a chain of exactly the given
length at the distinguished sandwich center. -/
theorem exists_convexHardyBallChain_at_center_of_length (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {c : Vec d} {rho Rad r : ℝ} (hrho : 0 < rho) (hRad : 0 ≤ Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad)
    {x : Vec d} (hx : x ∈ U) (N : ℕ)
    (hlower : r ≤ convexHardyBallChainRadius rho N 0)
    (hupper : convexHardyBallChainRadius rho N 0 < 2 * r) :
    ∃ chain : ConvexHardyBallChain U x rho Rad r,
      chain.center = c ∧ chain.length = N := by
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hsand : HasBallSandwich U rho Rad :=
    ⟨hrho, hRad, c, hinner, houter⟩
  have hrhoRad : rho ≤ Rad := HasBallSandwich.le_of_pos_dim hdpos hsand
  have hRadpos : 0 < Rad := lt_of_lt_of_le hrho hrhoRad
  let chain : ConvexHardyBallChain U x rho Rad r := {
    center := c
    length := N
    initial_radius_lower := hlower
    initial_radius_upper := hupper
    balls_subset := fun i =>
      euclideanBallAt_convexHardyBallChainCenter_subset hU.convex
        hrho hinner hx N i
    terminal_center := convexHardyBallChainCenter_last c x N
    terminal_radius := convexHardyBallChainRadius_last rho N
    radius_succ := convexHardyBallChainRadius_succ rho N
    initial_center_dist := by
      rw [dist_convexHardyBallChainCenter_zero]
      exact convexHardyBallChainCenter_dist_lt_at_center
        hrho hRadpos houter hx N 0
    center_dist_succ := fun i => by
      rw [dist_convexHardyBallChainCenter_succ]
      exact convexHardyBallChainCenter_dist_lt_at_center
        hrho hRadpos houter hx N i.castSucc }
  exact ⟨chain, rfl, rfl⟩

end

end HighContrast
end HCPolySupport
