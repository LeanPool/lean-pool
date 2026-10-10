/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyDomain
public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.ResonanceLoss
public import LeanPool.ArnoldKAM.Arnold1963.Step.Fundamental

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

theorem frequencyLossRadius_three (Θ β : ℝ≥0) :
    frequencyLossRadius Θ β (3 * β) = (5 + 7 * Θ) * β := by
  unfold frequencyLossRadius frequencyOuterRadius
  ring

theorem frequencyMeasureRadius_three (Θ β : ℝ≥0) :
    frequencyLossRadius Θ β (3 * β) + β = (6 + 7 * Θ) * β := by
  rw [frequencyLossRadius_three]
  ring

theorem neighborhood_subset_erosion_neighborhood {n : ℕ} (S : Set (ComplexSpace n))
    (r t : ℝ≥0) : closedBallNeighborhood S r ⊆ erosion (closedBallNeighborhood S (r + t)) t := by
  rintro x ⟨p, hp, hxp⟩ y hy
  exact ⟨p, hp, (dist_triangle y x p).trans (by
    change dist y x ≤ (t : ℝ) at hy
    change dist x p ≤ (r : ℝ) at hxp
    simp only [NNReal.coe_add]
    linarith)⟩

theorem neighborhood_conj {n : ℕ} {S : Set (ComplexSpace n)}
    (hS : ConjInvariant S) (r : ℝ≥0) : ConjInvariant (closedBallNeighborhood S r) := by
  rintro x ⟨p, hp, hxp⟩
  refine ⟨conjVec p, hS _ hp, ?_⟩
  simpa only [conjVec_eq_star, dist_star_star] using hxp

namespace FrequencyChangeInput
variable {n : ℕ} {A g Δ : ComplexSpace n → ComplexSpace n}
  {G Ω : Set (ComplexSpace n)} {β κ θ Θ : ℝ≥0}
  (h : FrequencyChangeInput A g Δ G Ω β κ θ Θ)

/-- The corrected action domain retained after finite resonance removal and erosion. -/
def iterationDomain (K N : ℝ) : Set (ComplexSpace n) :=
  h.innerDomain (nonresonantDomain Ω id K N) (3 * β)
/-- A closed-ball neighborhood of the retained inductive action domain. -/
def iterationE (K N : ℝ) : Set (ComplexSpace n) :=
  closedBallNeighborhood (h.iterationDomain K N) (3 * β)

theorem iterationChart (K N : ℝ) :
    AnalyticFrequencyChart (fun p => A p + Δ p) h.newInverse (h.iterationDomain K N)
      (erosion (nonresonantDomain Ω id K N) ((5 + 7 * Θ) * β)) := by
  have hh := h.innerChart (fun _ hx => hx.1)
    (isCompact_nonresonant_frequency_domain h.chart.image_compact K N)
    (nonresonantDomain_conj h.chart.image_conj (fun _ _ => rfl)) (3 * β)
  simpa only [iterationDomain, innerFrequency, frequencyLossRadius_three] using hh

theorem iterationE_subset (K N : ℝ) : h.iterationE K N ⊆ erosion G β :=
  (h.neighborhood_subset (fun _ hx => hx.1) (3 * β)).trans h.outer_subset

theorem iteration_derivative_bounds (K N : ℝ) {p} (hp : p ∈ h.iterationDomain K N)
    (v : ComplexSpace n) :
    ((θ : ℝ) * (1 - (κ : ℝ))) * ‖v‖ ≤ ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ∧
      ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ≤ ((Θ : ℝ) * (1 + (κ : ℝ))) * ‖v‖ :=
  h.new_derivative_bounds (h.inner_subset_outerDomain (fun _ hx => hx.1) (3 * β) hp) v

theorem iterationE_nonresonant (K N : ℝ) {p} (hp : p ∈ h.iterationE K N) :
    FiniteNonresonant (A p + Δ p) K N :=
  (h.neighborhood_maps (fun _ hx => hx.1) (3 * β) hp).2

theorem iterationE_compact (K N : ℝ) : IsCompact (h.iterationE K N) :=
  isCompact_closedBallNeighborhood (h.iterationChart K N).compact _

theorem iterationE_conj (K N : ℝ) : ConjInvariant (h.iterationE K N) :=
  neighborhood_conj (h.iterationChart K N).domain_conj _

theorem iteration_target_buffer (K N : ℝ) :
    closedBallNeighborhood (h.iterationDomain K N) β ⊆ erosion (h.iterationE K N) (β + β) := by
  have hh := neighborhood_subset_erosion_neighborhood (h.iterationDomain K N) β (β + β)
  have he : β + (β + β) = 3 * β := by ring
  simpa only [he, iterationE] using hh

theorem iteration_measure (K N : ℝ) :
    realVolume (G \ h.iterationDomain K N) ≤ ENNReal.ofReal ((θ : ℝ)⁻¹ ^ n) *
      realVolume (Ω \ erosion (nonresonantDomain Ω id K N) ((6 + 7 * Θ) * β)) := by
  have hh := h.measure_loss (fun _ hx => hx.1)
    (isCompact_nonresonant_frequency_domain h.chart.image_compact K N) (3 * β)
  simpa only [iterationDomain, frequencyMeasureRadius_three] using hh

theorem fundamentalInput {ρ δ γ : ℝ≥0} {K M T : ℝ}
    {Hbar : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n (erosion G β) ρ}
    (hi : IntegrableData Hbar (erosion G β) T)
    (hfreq : ∀ p ∈ erosion G β, actionFrequency Hbar p = A p + Δ p)
    (hb : FundamentalParameters n ρ β δ γ K (2 * M) T)
    (hf : f.uniformNorm ≤ 2 * M) (hzero : ∀ p ∈ erosion G β, f.angleAverage p = 0) :
    FundamentalInput (E := h.iterationE K (fundamentalCutoff γ (2 * M)))
      (β := β) (δ := δ) (γ := γ) (K := K) (M := 2 * M) (Θ := T) Hbar f where
  integrable := hi
  domain_subset := h.iterationE_subset _ _
  domain_conj := h.iterationE_conj _ _
  perturbation_bound := hf
  mean_zero := fun _ hp => hzero _ (h.iterationE_subset _ _ hp)
  nonresonant := by
    intro p hp
    rw [hfreq _ (h.iterationE_subset _ _ hp)]
    exact h.iterationE_nonresonant _ _ hp
  budget := hb

end FrequencyChangeInput

theorem frequency_iteration_next_chart {n : ℕ} {K N₀ N : ℝ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {G Ωbase : Set (ComplexSpace n)}
    {β κ θ Θ : ℝ≥0} (s : ResonanceDomainState n K N₀)
    (h : FrequencyChangeInput A g Δ G (s.domain Ωbase) β κ θ Θ)
    (hK : 0 < K) (hNN : N₀ ≤ N) :
    AnalyticFrequencyChart (fun p => A p + Δ p) h.newInverse (h.iterationDomain K N)
      ((s.next hK hNN ((5 + 7 * Θ) * β)).domain Ωbase) := by
  rw [s.next_domain]
  exact h.iterationChart K N

theorem frequency_iteration_measure_budget {n : ℕ} {K N₀ N D : ℝ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {G Ωbase : Set (ComplexSpace n)}
    {β κ θ Θ : ℝ≥0} (s : ResonanceDomainState n K N₀)
    (h : FrequencyChangeInput A g Δ G (s.domain Ωbase) β κ θ Θ)
    (hD : TypeD Ωbase D) (hn : 0 < n) (hK : 0 < K)
    (hN₀ : 1 ≤ N₀) (hN : 1 < N) (hNN : N₀ ≤ N) :
    realVolume (G \ h.iterationDomain K N) ≤ ENNReal.ofReal ((θ : ℝ)⁻¹ ^ n) *
      (ENNReal.ofReal (resonanceLossConstant n * D *
        (K * newShellBudget N₀ N + (((6 + 7 * Θ) * β : ℝ≥0) : ℝ) * N ^ n)) * realVolume Ωbase) :=
  (h.iteration_measure K N).trans (mul_le_mul' le_rfl
    (hD.ar_loss_le s hn hK hN₀ hN hNN ((6 + 7 * Θ) * β)))

end KamProject.Arnold1963
