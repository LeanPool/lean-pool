/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Consistency.AdmissibleTests
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient

/-!
# High-contrast homogenization: Analytic.AntiVacuityInstances

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The admissible-test families at the domains the estimates read

The two dual-norm estimates of
`t.random.homogenization` are read on two concrete
families of domains: the bounded convex domains carrying the Dirichlet estimate
`e.random.dirichlet`, and the ellipsoids
`E_r` of `e.homogenized.ellipsoids` carrying the
corrector estimate `e.random.corrector`.
This module instantiates the general nonemptiness of the admissible-test family
at exactly those two domain classes, so neither estimate is satisfied by the
absence of anything to estimate.

The one geometric ingredient is a bridge between the ambient supremum metric,
in which the smooth bump of the witness is built, and the Euclidean radii in
which the domains are described: a supremum-norm ball of radius `r / √d` sits
inside the Euclidean ball of radius `r`, since a Euclidean square norm is at most
`d` times the square of the supremum norm.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A sup-norm ball of radius `r / √d` sits inside the Euclidean ball of radius
`r`; this is the bridge between the ambient metric and the Euclidean radii. -/
theorem metricBall_subset_euclideanBallAt (hd : 0 < d) (c : Vec d) {r : ℝ}
    (hr : 0 < r) :
    Metric.ball c (r / Real.sqrt d) ⊆ euclideanBallAt c r := by
  intro x hx
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsq : Real.sqrt d > 0 := Real.sqrt_pos.2 hdpos
  have hnorm : ‖x - c‖ < r / Real.sqrt d := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    exact hx
  have h1 : vecNormSq (x - c) ≤ (d : ℝ) * ‖x - c‖ ^ 2 :=
    vecNormSq_le_dim_mul_norm_sq (x - c)
  have h2 : ‖x - c‖ ^ 2 < (r / Real.sqrt d) ^ 2 := by
    have hnn : 0 ≤ ‖x - c‖ := norm_nonneg _
    exact pow_lt_pow_left₀ hnorm hnn two_ne_zero
  have h3 : (d : ℝ) * (r / Real.sqrt d) ^ 2 = r ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hdpos)]
    field_simp
  show vecNormSq (x - c) < r ^ 2
  calc vecNormSq (x - c) ≤ (d : ℝ) * ‖x - c‖ ^ 2 := h1
    _ < (d : ℝ) * (r / Real.sqrt d) ^ 2 := by
        exact mul_lt_mul_of_pos_left h2 hdpos
    _ = r ^ 2 := h3

/-- The ellipsoid contains a sup-norm ball about the origin. -/
theorem exists_metricBall_subset_ellipsoid (hd : 0 < d) (abar : Mat d) {r : ℝ}
    (hr : 0 < r) :
    ∃ (c : Vec d) (ε : ℝ), 0 < ε ∧ Metric.ball c ε ⊆ ellipsoid abar r := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨(0 : Vec d), r / Real.sqrt d, by positivity, ?_⟩
  exact (metricBall_subset_euclideanBallAt hd (0 : Vec d) hr).trans
    (euclideanBallAt_zero_subset_ellipsoid abar r)

/-- **The admissible-test family of the corrector estimate is not empty.**  The
family of the `H̲^{-1}` dual norm on an ellipsoid contains a nonzero field, so
the estimate `e.random.corrector` is not
satisfied by the absence of anything to estimate. -/
theorem exists_nonzero_admissible_test_h1_ellipsoid (hd : 0 < d) {abar : Mat d}
    (hS : (symmPart abar).PosDef) {r : ℝ} (hr : 0 < r) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest (ellipsoid abar r) ψ ∧ ψ ≠ 0 ∧
      h1NormSq (ellipsoid abar r) ψ ≤ 1 :=
  exists_nonzero_admissible_test_h1_of_ball hd (isBoundedDomain_ellipsoid hS r)
    (exists_metricBall_subset_ellipsoid hd abar hr)

/-- **The admissible-test family of the Dirichlet estimate is not empty**, at the
domains that estimate binds: a bounded open convex domain whose shape datum is a
concentric ball sandwich. -/
theorem exists_nonzero_admissible_test_convex (hd : 0 < d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {ρ Rad : ℝ}
    (hsw : HasBallSandwich U ρ Rad) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 ∧ hsNormSq U s ψ ≤ 1 := by
  have hne : U.Nonempty := by
    obtain ⟨hρ, -, c, hin, -⟩ := hsw
    exact ⟨c, hin (center_mem_euclideanBallAt c hρ)⟩
  exact exists_nonzero_admissible_test hd hU hne hs

end

end HighContrast
end HCPolySupport
