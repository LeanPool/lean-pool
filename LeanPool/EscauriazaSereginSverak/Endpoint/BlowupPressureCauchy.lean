/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarTime

/-!
# Blowup Pressure Cauchy

Pressure bounds and convergence estimates for the rescaled sequence.
-/

public section

open Filter
noncomputable section
namespace ESS

/-- Convergent near pressures and uniformly vanishing far pressures give a
strong local pressure limit. This is the two-radius argument in
`prop:blowup-limit`. -/
theorem blowup_pressure_limit_of_near_far
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (p : ℕ → E) (near far : ℕ → ℕ → E)
    (hsplit : ∀ L k, p k = near L k + far L k)
    (hnear : ∀ L, CauchySeq (near L))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ k, ‖far L k‖ < ε) :
    ∃ q : E, Tendsto p atTop (nhds q) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨L, hL⟩ := hfar (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp (hnear L))
    (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [hsplit L m, hsplit L n]
  have hdist : dist (near L m + far L m) (near L n + far L n) ≤
      dist (near L m) (near L n) + ‖far L m‖ + ‖far L n‖ := by
    calc
      dist (near L m + far L m) (near L n + far L n) ≤
          dist (near L m + far L m) (near L n + far L m) +
            dist (near L n + far L m) (near L n + far L n) :=
        dist_triangle _ _ _
      _ = dist (near L m) (near L n) + dist (far L m) (far L n) := by
        rw [dist_add_right, dist_add_left]
      _ ≤ dist (near L m) (near L n) +
            (‖far L m‖ + ‖far L n‖) := by
        have hnorm : dist (far L m) (far L n) ≤
            ‖far L m‖ + ‖far L n‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
        simpa only [add_comm] using
          (add_le_add_left hnorm (dist (near L m) (near L n)))
      _ = _ := by ring
  have hnear' := hN m hm n hn
  have hfarM := hL m
  have hfarN := hL n
  linarith only [hdist, hnear', hfarM, hfarN]

end ESS
