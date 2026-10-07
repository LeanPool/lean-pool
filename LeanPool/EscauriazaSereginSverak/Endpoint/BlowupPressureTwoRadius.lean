/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszTimeLocal
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszNear

/-!
# Blowup Pressure Two Radius

Pressure bounds and convergence estimates for the rescaled sequence.
-/

public section

open Filter
noncomputable section
namespace ESS

/-- Convergent near pressures and uniformly small far pressures identify the
limit of the full pressure through the two-radius argument. -/
theorem blowup_pressure_two_radius_convergence
    {E : Type*} [NormedAddCommGroup E]
    (p : ℕ → E) (q : E)
    (near : ℕ → ℕ → E) (nearLimit : ℕ → E)
    (far : ℕ → ℕ → E) (farLimit : ℕ → E)
    (hsplit : ∀ L k, p k = near L k + far L k)
    (hlimitSplit : ∀ L, q = nearLimit L + farLimit L)
    (hnear : ∀ L, Tendsto (near L) atTop (nhds (nearLimit L)))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ,
      (∀ k, ‖far L k‖ < ε) ∧ ‖farLimit L‖ < ε) :
    Tendsto p atTop (nhds q) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨L, hLk, hLu⟩ := hfar (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((hnear L).eventually (Metric.ball_mem_nhds (nearLimit L)
      (by positivity : 0 < ε / 3)))
  refine ⟨N, fun k hk => ?_⟩
  rw [hsplit L k, hlimitSplit L]
  have hdist : dist (near L k + far L k) (nearLimit L + farLimit L) ≤
      dist (near L k) (nearLimit L) + ‖far L k‖ + ‖farLimit L‖ := by
    calc
      dist (near L k + far L k) (nearLimit L + farLimit L) ≤
          dist (near L k + far L k) (nearLimit L + far L k) +
            dist (nearLimit L + far L k) (nearLimit L + farLimit L) :=
        dist_triangle _ _ _
      _ = dist (near L k) (nearLimit L) +
          dist (far L k) (farLimit L) := by
        rw [dist_add_right, dist_add_left]
      _ ≤ dist (near L k) (nearLimit L) +
          (‖far L k‖ + ‖farLimit L‖) := by
        gcongr
        rw [dist_eq_norm]
        exact norm_sub_le _ _
      _ = _ := by ring
  have hnear' : dist (near L k) (nearLimit L) < ε / 3 :=
    Metric.mem_ball.mp (hN k hk)
  have hfar' := hLk k
  linarith only [hdist, hnear', hfar', hLu]

end ESS
