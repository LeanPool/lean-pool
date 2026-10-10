/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Estimates
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.LimitDomain
public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Budgets

/-!
Cumulative transformation estimates. Mean-value arguments first establish segment containment
in the relevant domain.
-/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem phase_antitone : Antitone (h.phase b) :=
  antitone_nat_of_succ_le (fun s => (h.phase_buffer b s).trans (erosion_subset _ _))

theorem phase_closed (s : ℕ) : IsClosed (h.phase b s) := by
  have hc : Continuous (fun q : ComplexSpace n => ‖imagPart q‖) := by
    unfold imagPart
    fun_prop
  exact (h.domain_compact b s).isClosed.prod (isClosed_le hc continuous_const)

/-- The intersection of all phase domains in the iteration. -/
def limitPhase : Set (ComplexPhaseSpace n) := ⋂ s, h.phase b s

theorem limitPhase_subset (s : ℕ) : h.limitPhase b ⊆ h.phase b s := iInter_subset _ s

theorem commonPhase_subset : phaseDomain (h.limitDomain b) (ρ₀ / 3) ⊆ h.limitPhase b := by
  intro z hz
  apply mem_iInter.mpr
  intro s
  refine ⟨h.limit_subset b s hz.1, ?_⟩
  have hq : ‖imagPart z.2‖ ≤ (ρ₀ : ℝ) / 3 := hz.2
  exact hq.trans (InitialData.width_gt_third b s).le

theorem cumulative_analytic (s : ℕ) : AnalyticOnNhd ℂ (h.cumulative b s) (h.phase b s) := by
  induction s with
  | zero => exact fun _ _ => analyticAt_id
  | succ s ih =>
    intro z hz
    exact (ih _ ((h.transformation b s).mapsTo hz)).comp ((h.transformation b s).analytic z hz)

theorem cumulative_derivative (s : ℕ) :
    ∀ z ∈ h.phase b s, ‖fderiv ℂ (h.cumulative b s) z‖ ≤ (2 : ℝ) ^ s := by
  induction s with
  | zero =>
    intro z _
    simpa only [cumulative, fderiv_id, pow_zero] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := ComplexPhaseSpace n))
  | succ s ih =>
    intro z hz
    change ‖fderiv ℂ (h.cumulative b s ∘ (h.transformation b s).toFun) z‖ ≤ _
    rw [fderiv_comp z
      ((h.cumulative_analytic b s) _ ((h.transformation b s).mapsTo hz)).differentiableAt
      ((h.transformation b s).analytic z hz).differentiableAt, pow_succ]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (ih _ ((h.transformation b s).mapsTo hz))
        ((h.transformation b s).derivative_bound z hz).le (norm_nonneg _) (by positivity))

theorem cumulative_canonical (s : ℕ) : CanonicalOn (h.cumulative b s) (h.phase b s) := by
  induction s with
  | zero => exact fun z _ => canonicalAt_id z
  | succ s ih => exact ih.comp (h.transformation b s).canonical (h.transformation b s).mapsTo

theorem cumulative_injOn (s : ℕ) : InjOn (h.cumulative b s) (h.phase b s) := by
  induction s with
  | zero => exact fun _ _ _ _ hh => hh
  | succ s ih => exact ih.comp (h.transformation b s).injOn (h.transformation b s).mapsTo

theorem cumulative_increment (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) :
    ‖h.cumulative b (s + 1) z - h.cumulative b s z‖ ≤ (2 : ℝ) ^ s * beta δ₁ s := by
  have hm : (h.transformation b s).toFun z ∈ closedBall z (beta δ₁ s : ℝ) := by
    rw [mem_closedBall, dist_eq_norm]
    exact (h.displacement_lt b s hz).le
  have hseg : segment ℝ z ((h.transformation b s).toFun z) ⊆ h.phase b s :=
    ((convex_closedBall z (beta δ₁ s : ℝ)).segment_subset
      (mem_closedBall_self (beta δ₁ s).coe_nonneg) hm).trans (h.phase_buffer b s hz)
  exact (norm_sub_le_of_analytic_segment_bound hseg (h.cumulative_analytic b s)
    ⟨by positivity, h.cumulative_derivative b s⟩).trans
    (mul_le_mul_of_nonneg_left (h.displacement_lt b s hz).le (by positivity))

theorem cumulative_periodic (s : ℕ) : ∀ z ∈ h.phase b s, ∀ k : FourierIndex n,
    h.cumulative b s (phaseShift k z) = phaseShift k (h.cumulative b s z) := by
  induction s with
  | zero => exact fun _ _ _ => rfl
  | succ s ih =>
    intro z hz k
    change h.cumulative b s ((h.transformation b s).toFun (phaseShift k z)) = _
    rw [h.transformation_periodic b s hz k]
    exact ih _ ((h.transformation b s).mapsTo hz) k

theorem cumulative_real (s : ℕ) : ∀ z ∈ h.phase b s,
    h.cumulative b s (conjPhase z) = conjPhase (h.cumulative b s z) := by
  induction s with
  | zero => exact fun _ _ => rfl
  | succ s ih =>
    intro z hz
    change h.cumulative b s ((h.transformation b s).toFun (conjPhase z)) = _
    rw [h.transformation_real b s hz]
    exact ih _ ((h.transformation b s).mapsTo hz)

theorem limitPhase_shift {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b)
    (k : FourierIndex n) : phaseShift k z ∈ h.limitPhase b := by
  apply mem_iInter.mpr
  intro s
  exact (phaseShift_mem_phaseDomain k z).mpr (h.limitPhase_subset b s hz)

theorem limitPhase_conj {z : ComplexPhaseSpace n} (hz : z ∈ h.limitPhase b) :
    conjPhase z ∈ h.limitPhase b := by
  apply mem_iInter.mpr
  intro s
  exact conj_mem_phaseDomain (h.state b s).input.chart.domain_conj (h.limitPhase_subset b s hz)

end KamProject.Arnold1963.Iteration.InitialData
