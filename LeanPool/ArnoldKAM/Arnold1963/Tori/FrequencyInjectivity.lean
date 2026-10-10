/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Nonresonance
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.MeanValue

/-!
Injectivity of limit frequency labels. Inverse mean-value estimates are taken on contained
frequency balls, without assuming convexity of the limiting action domain.
-/

@[expose] public section
noncomputable section
open Set Filter Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

@[simp] theorem frequencyDomain_zero : h.frequencyDomain b 0 = Ω₀ := by
  exact ResonanceDomainState.initial_domain n (κ * (δ₁ : ℝ)) Ω₀

theorem limitFrequency_ball_subset {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (s : ℕ) : closedBall (h.limitFrequency b p) (beta δ₁ s : ℝ) ⊆
      h.frequencyDomain b s := by
  have hm := h.limitFrequency_mem b hp (s + 1)
  rw [h.frequencyDomain_succ b] at hm
  intro y hy
  apply (hm (show y ∈ closedBall (h.limitFrequency b p)
      (((5 + 7 * Iteration.upper Θ₀ δ₁ s) * beta δ₁ s : ℝ≥0) : ℝ) from ?_)).1
  rw [mem_closedBall] at hy ⊢
  apply hy.trans
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
  have hu := (Iteration.upper Θ₀ δ₁ s).coe_nonneg
  have hb := (beta δ₁ s).coe_nonneg
  nlinarith

private theorem inverse_frequency_ball_bound {p : ComplexSpace n}
    (hp : p ∈ h.limitDomain b) (s : ℕ) {x y : ComplexSpace n}
    (hx : x ∈ closedBall (h.limitFrequency b p) (beta δ₁ s : ℝ))
    (hy : y ∈ closedBall (h.limitFrequency b p) (beta δ₁ s : ℝ)) :
    ‖(h.state b s).inverseFrequency y - (h.state b s).inverseFrequency x‖ ≤
      ((θ₀ : ℝ) / 2)⁻¹ * ‖y - x‖ := by
  exact norm_sub_le_of_analytic_segment_bound
    (((convex_closedBall _ _).segment_subset hx hy).trans (h.limitFrequency_ball_subset b hp s))
    (h.state b s).input.chart.inverse_analytic
    ⟨by positivity, fun z hz => (h.state b s).input.chart.inverse_derivative_le
      (by exact div_pos b.lower_pos (by norm_num))
      (fun q hq v => (h.frequency_bounds b s hq v).1) hz⟩

theorem limitFrequency_injOn : InjOn (h.limitFrequency b) (h.limitDomain b) := by
  intro p hp q hq he
  have hb : ∀ s, ‖q - p‖ ≤ ((θ₀ : ℝ) / 2)⁻¹ * (beta δ₁ s : ℝ) := by
    intro s
    have hps := h.limitFrequency_tail b hp s
    have hqs := h.limitFrequency_tail b hq s
    have hpc : h.frequency b s p ∈ closedBall (h.limitFrequency b p) (beta δ₁ s : ℝ) := by
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      linarith [(beta δ₁ s).coe_nonneg]
    have hqc : h.frequency b s q ∈ closedBall (h.limitFrequency b p) (beta δ₁ s : ℝ) := by
      rw [he, mem_closedBall, dist_eq_norm, norm_sub_rev]
      linarith [(beta δ₁ s).coe_nonneg]
    have hi := h.inverse_frequency_ball_bound b hp s hpc hqc
    have hleftp := (h.state b s).input.chart.left (h.limit_subset b s hp)
    have hleftq := (h.state b s).input.chart.left (h.limit_subset b s hq)
    change (h.state b s).inverseFrequency (h.frequency b s p) = p at hleftp
    change (h.state b s).inverseFrequency (h.frequency b s q) = q at hleftq
    rw [hleftp, hleftq] at hi
    apply hi.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (h.frequency b s q) (h.limitFrequency b p) (h.frequency b s p)
    rw [he, norm_sub_rev (h.frequency b s q) (h.limitFrequency b q)] at ht
    rw [he] at hps
    linarith
  have hz : ‖q - p‖ ≤ 0 := ge_of_tendsto
    (by simpa using b.beta_summable.tendsto_atTop_zero.const_mul (((θ₀ : ℝ) / 2)⁻¹))
    (Eventually.of_forall hb)
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))).symm

/-- The image of the limiting action domain under the limiting frequency map. -/
def retainedFrequencies : Set (ComplexSpace n) := h.limitFrequency b '' h.limitDomain b

/-- A set-restricted inverse assigning action labels to retained limiting frequencies. -/
def frequencyLabel : ComplexSpace n → ComplexSpace n :=
  Function.invFunOn (h.limitFrequency b) (h.limitDomain b)

theorem frequencyLabel_left {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    h.frequencyLabel b (h.limitFrequency b p) = p :=
  (h.limitFrequency_injOn b).leftInvOn_invFunOn hp

theorem frequencyLabel_mem {ω : ComplexSpace n} (hω : ω ∈ h.retainedFrequencies b) :
    h.frequencyLabel b ω ∈ h.limitDomain b := (Function.invFunOn_pos hω).1

theorem frequencyLabel_right {ω : ComplexSpace n} (hω : ω ∈ h.retainedFrequencies b) :
    h.limitFrequency b (h.frequencyLabel b ω) = ω := (Function.invFunOn_pos hω).2

/-- The original action center corresponding to a frequency through the initial inverse chart. -/
def unperturbedCenter (ω : ComplexSpace n) : ComplexSpace n := h.inverseFrequency ω

theorem unperturbedCenter_mem {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    h.unperturbedCenter (h.limitFrequency b p) ∈ h.domain :=
  h.chart.inverse_maps (by simpa using h.limitFrequency_mem b hp 0)

theorem unperturbedCenter_displacement {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    ‖h.unperturbedCenter (h.limitFrequency b p) - p‖ <
      (θ₀ : ℝ)⁻¹ * ((beta δ₁ 0 : ℝ) / 2) := by
  have hp0 : p ∈ h.domain := h.limit_subset b 0 hp
  have ht := h.limitFrequency_tail b hp 0
  have hc : h.frequency b 0 p ∈ closedBall (h.limitFrequency b p) (beta δ₁ 0 : ℝ) := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    linarith [(beta δ₁ 0).coe_nonneg]
  have hm := norm_sub_le_of_analytic_segment_bound
    (((convex_closedBall _ _).segment_subset hc (mem_closedBall_self (beta δ₁ 0).coe_nonneg)).trans
      (show closedBall (h.limitFrequency b p) (beta δ₁ 0 : ℝ) ⊆ Ω₀ by
        simpa using h.limitFrequency_ball_subset b hp 0))
    h.chart.inverse_analytic
    ⟨inv_nonneg.mpr θ₀.coe_nonneg, fun z hz => h.chart.inverse_derivative_le b.lower_pos h.lower hz⟩
  change ‖h.inverseFrequency (h.limitFrequency b p) -
    h.inverseFrequency (actionFrequency h.integrable p)‖ ≤ _ at hm
  rw [h.chart.left hp0] at hm
  exact hm.trans_lt (mul_lt_mul_of_pos_left ht (inv_pos.mpr b.lower_pos))

end KamProject.Arnold1963.Iteration.InitialData
