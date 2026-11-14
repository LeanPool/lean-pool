/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Distribution.Feller
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Existence of a stationary agent distribution

Krylov–Bogolyubov, for the income fluctuation problem: average the iterates of the
distribution operator, and any cluster point of those averages is stationary.

The two ingredients are both already in place. The space of probability measures over the
compact state space is compact, by Prokhorov; and the operator is weakly continuous, by the
Feller property. What the averaging adds is that the *difference* between an average and
its image telescopes, so it vanishes in the limit even though the individual iterates need
not converge at all.
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- The state space is nonempty: a household at the borrowing limit is in it. This has to be
given by hand, since `assetFloor ≤ assetCap` is data carried by `P` rather than an instance. -/
instance instNonemptyState : Nonempty P.State :=
  ⟨⟨⟨assetFloor, ⟨le_refl assetFloor, P.assetFloor_le_assetCap⟩⟩, Classical.ofNonempty⟩⟩

/-- The average of the first `n + 1` iterates of the distribution operator. -/
noncomputable def cesaro (μ₀ : ProbabilityMeasure P.State) (n : ℕ) : Measure P.State :=
  (((n : ℝ≥0∞) + 1))⁻¹ • ∑ k ∈ Finset.range (n + 1),
    ((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State)

instance isProbabilityMeasure_cesaro (μ₀ : ProbabilityMeasure P.State) (n : ℕ) :
    IsProbabilityMeasure (P.cesaro μ₀ n) := by
  constructor
  have hsum : (∑ k ∈ Finset.range (n + 1),
      ((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State)) univ
      = (n : ℝ≥0∞) + 1 := by
    rw [Measure.finsetSum_apply]
    simp [measure_univ]
  rw [cesaro, Measure.smul_apply, hsum, smul_eq_mul]
  refine ENNReal.inv_mul_cancel (by positivity) (by simp)

/-- The integral against a Cesàro average is the average of the integrals. -/
theorem integral_cesaro (μ₀ : ProbabilityMeasure P.State) (n : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, h s ∂(P.cesaro μ₀ n)
      = (↑(n + 1))⁻¹ * ∑ k ∈ Finset.range (n + 1),
          ∫ s, h s ∂((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State) := by
  rw [cesaro, integral_smul_measure, integral_finsetSum_measure]
  · push_cast
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]
    simp [smul_eq_mul]
  · intro k _
    exact h.integrable _

/-- Integration against a bounded continuous function is weakly continuous. -/
theorem continuous_integral_bcf (h : P.State →ᵇ ℝ) :
    Continuous fun ν : ProbabilityMeasure P.State => ∫ s, h s ∂(ν : Measure P.State) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_id : Filter.Tendsto id (𝓝 μ) (𝓝 μ)) h

omit [BorelSpace Z] in
theorem abs_integral_le (ν : Measure P.State) [IsProbabilityMeasure ν] (h : P.State →ᵇ ℝ) :
    |∫ s, h s ∂ν| ≤ ‖h‖ := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖h‖) ?_).trans_eq ?_
  · filter_upwards with s using h.norm_coe_le_norm s
  · simp

/-- Applying the operator to the test function advances the measure by one period. -/
theorem integral_markovOp_iterate (μ₀ : ProbabilityMeasure P.State) (k : ℕ)
    (h : P.State →ᵇ ℝ) :
    ∫ s, P.markovOp h s ∂((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
      = ∫ s, h s ∂((P.pushProb^[k + 1] μ₀ : ProbabilityMeasure P.State) : Measure P.State) := by
  rw [Function.iterate_succ_apply', P.coe_pushProb]
  exact (P.integral_push _ h).symm

/-- **The telescoping estimate.** The average and its image differ by a single boundary
term over `n + 1`, which is the whole point of averaging: the individual iterates need not
converge, but this difference must vanish. -/
theorem integral_cesaro_sub (μ₀ : ProbabilityMeasure P.State) (n : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, P.markovOp h s ∂(P.cesaro μ₀ n) - ∫ s, h s ∂(P.cesaro μ₀ n)
      = (↑(n + 1))⁻¹ *
        (∫ s, h s ∂((P.pushProb^[n + 1] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
          - ∫ s, h s ∂(μ₀ : Measure P.State)) := by
  rw [P.integral_cesaro μ₀ n (P.markovOp h), P.integral_cesaro μ₀ n h, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  have hstep : ∀ k ∈ Finset.range (n + 1),
      (∫ s, P.markovOp h s ∂((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State))
        - ∫ s, h s ∂((P.pushProb^[k] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
      = (fun j => ∫ s, h s
            ∂((P.pushProb^[j] μ₀ : ProbabilityMeasure P.State) : Measure P.State)) (k + 1)
        - (fun j => ∫ s, h s
            ∂((P.pushProb^[j] μ₀ : ProbabilityMeasure P.State) : Measure P.State)) k :=
    fun k _ => by rw [P.integral_markovOp_iterate]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_range_sub (fun j => ∫ s, h s
      ∂((P.pushProb^[j] μ₀ : ProbabilityMeasure P.State) : Measure P.State))]
  simp

theorem tendsto_cesaro_sub (μ₀ : ProbabilityMeasure P.State) (h : P.State →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, P.markovOp h s ∂(P.cesaro μ₀ n) - ∫ s, h s ∂(P.cesaro μ₀ n))
      atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      ‖∫ s, P.markovOp h s ∂(P.cesaro μ₀ n) - ∫ s, h s ∂(P.cesaro μ₀ n)‖
        ≤ (((n : ℝ) + 1))⁻¹ * (2 * ‖h‖) := by
    intro n
    rw [Real.norm_eq_abs, P.integral_cesaro_sub μ₀ n h, abs_mul]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_sub _ _).trans ?_
    have h1 := P.abs_integral_le
      ((P.pushProb^[n + 1] μ₀ : ProbabilityMeasure P.State) : Measure P.State) h
    have h2 := P.abs_integral_le ((μ₀ : ProbabilityMeasure P.State) : Measure P.State) h
    linarith
  refine squeeze_zero_norm hbound ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (2 * ‖h‖))

/-- **Krylov–Bogolyubov: a stationary agent distribution exists.** Average the iterates and
take a cluster point, which exists because the space of probability measures over the
compact state space is compact. The telescoping estimate makes that cluster point
stationary. -/
theorem exists_isStationary (μ₀ : ProbabilityMeasure P.State) :
    ∃ μ : ProbabilityMeasure P.State, P.IsStationary μ := by
  set ν : ℕ → ProbabilityMeasure P.State := fun n => ⟨P.cesaro μ₀ n, inferInstance⟩ with hν
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map ν atTop)
  refine ⟨μ, ?_⟩
  have key : ∀ h : P.State →ᵇ ℝ,
      ∫ s, h s ∂((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State)
        = ∫ s, h s ∂(μ : Measure P.State) := by
    intro h
    set g : ProbabilityMeasure P.State → ℝ := fun ρ =>
      ∫ s, P.markovOp h s ∂(ρ : Measure P.State) - ∫ s, h s ∂(ρ : Measure P.State) with hg
    have hgc : Continuous g :=
      (P.continuous_integral_bcf _).sub (P.continuous_integral_bcf _)
    have hgt : Filter.map (g ∘ ν) atTop ≤ 𝓝 0 := P.tendsto_cesaro_sub μ₀ h
    have hcl : ClusterPt (g μ) (Filter.map (g ∘ ν) atTop) := by
      rw [← Filter.map_map]
      exact hμ.map hgc.continuousAt le_rfl
    have hz : g μ = 0 := by
      by_contra hne
      have hdisj : Disjoint (𝓝 (g μ)) (𝓝 (0 : ℝ)) := disjoint_nhds_nhds.mpr hne
      have : (𝓝 (g μ) ⊓ Filter.map (g ∘ ν) atTop).NeBot := hcl
      exact (this.mono (inf_le_inf_left _ hgt)).ne (_root_.disjoint_iff.mp hdisj)
    have := P.integral_push (μ : Measure P.State) h
    simp only [hg, sub_eq_zero] at hz
    rw [P.coe_pushProb, this, hz]
  have hfin : (P.pushProb μ).toFiniteMeasure = μ.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq key
  exact ProbabilityMeasure.toMeasure_injective
    (congrArg (fun x : FiniteMeasure P.State => (x : Measure P.State)) hfin)

end IncomeFluctuation

end LeanEconomics
