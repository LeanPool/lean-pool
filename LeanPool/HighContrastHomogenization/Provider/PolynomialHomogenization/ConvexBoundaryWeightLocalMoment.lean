/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistanceMonotone
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightMoment
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyLocalLayer

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local negative moments of convex boundary distance

The global negative-moment estimate is applied to a doubled ball
localization. Monotonicity of boundary distance then controls the original
domain weight on the smaller localization.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem boundedConvexDomain_compl_nonempty
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : Uᶜ.Nonempty := by
  let : Nonempty (Fin d) := Fintype.card_pos_iff.mp (by simpa using! hd)
  apply Set.nonempty_compl.mpr
  intro hUuniv
  apply NormedSpace.unbounded_univ (𝕜 := ℝ) (E := Vec d)
  simpa only [hUuniv] using hU.isBoundedDomain.isBounded

/-- On a smaller open bounded convex domain, the negative boundary-distance
weight dominates that of the larger domain. -/
theorem euclideanBoundaryWeight_mono_of_subset (hd : 1 ≤ d)
    {V U : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {p : ℝ} (hp : 0 ≤ p) {x : Vec d} (hx : x ∈ V) :
    euclideanBoundaryWeight U p x ≤ euclideanBoundaryWeight V p x := by
  unfold euclideanBoundaryWeight
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_nonpos
  · exact euclideanBoundaryDistance_pos hd hV hx
  · exact euclideanBoundaryDistance_mono hVU
      (boundedConvexDomain_compl_nonempty hd hU) x
  · exact neg_nonpos.mpr hp

/-- A ball localization has the scale-correct negative boundary-distance
moment, expressed using the volume of its doubled metric ball. -/
theorem lintegral_local_euclideanBoundaryWeight_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad r p : ℝ} (hsand : HasBallSandwich U rho Rad)
    (hr : 0 < r) (hrRad : r ≤ Rad) (hp0 : 0 < p) (hp1 : p < 1)
    {z : Vec d} (hne : (U ∩ euclideanBallAt z r).Nonempty) :
    ∫⁻ x in U ∩ euclideanBallAt z r,
        euclideanBoundaryWeight U p x ∂volume ≤
      volume (Metric.ball z (2 * r)) *
        ENNReal.ofReal ((((d : ℝ) /
          (r * rho / (4 * (rho + Rad)))) ^ p) / (1 - p)) := by
  let V : Set (Vec d) := U ∩ Metric.ball z (2 * r)
  have hV : IsOpenBoundedConvexDomain V := by
    dsimp only [V]
    exact IsOpenBoundedConvexDomain.inter_metricBall hU z (2 * r)
  have hsandV : HasBallSandwich V
      (r * rho / (4 * (rho + Rad))) ((4 * r) * Real.sqrt d) := by
    dsimp only [V]
    exact hasBallSandwich_inter_metricBall hd hU hsand hr hrRad hne
  have hAV : U ∩ euclideanBallAt z r ⊆ V := by
    rintro x ⟨hxU, hxz⟩
    refine ⟨hxU, ?_⟩
    apply Metric.ball_subset_ball (by linarith only [hr] : r ≤ 2 * r)
    exact euclideanBallAt_subset_metricBall z hr hxz
  calc
    (∫⁻ x in U ∩ euclideanBallAt z r,
        euclideanBoundaryWeight U p x ∂volume) ≤
        ∫⁻ x in U ∩ euclideanBallAt z r,
          euclideanBoundaryWeight V p x ∂volume := by
      exact setLIntegral_mono'
        (hU.isOpen.measurableSet.inter (isOpen_euclideanBallAt z r).measurableSet)
        fun x hx => euclideanBoundaryWeight_mono_of_subset hd hV hU
          Set.inter_subset_left hp0.le (hAV hx)
    _ ≤ ∫⁻ x in V, euclideanBoundaryWeight V p x ∂volume :=
      lintegral_mono_set hAV
    _ ≤ volume V * ENNReal.ofReal ((((d : ℝ) /
          (r * rho / (4 * (rho + Rad)))) ^ p) / (1 - p)) :=
      lintegral_euclideanBoundaryWeight_le hd hV hsandV hp0 hp1
    _ ≤ volume (Metric.ball z (2 * r)) *
        ENNReal.ofReal ((((d : ℝ) /
          (r * rho / (4 * (rho + Rad)))) ^ p) / (1 - p)) := by
      exact mul_le_mul_left (by
        simpa only [V] using measure_mono Set.inter_subset_right) _

end

end HighContrast
end HCPolySupport
