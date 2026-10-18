/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationAugmented
public import LeanPool.AiyagariEquilibrium.Equilibrium.Aiyagari


/-!
# Capital supply is continuous, and the equilibrium theorem applies

`exists_aiyagari_equilibrium` has carried one hypothesis since it was proved: that capital
supply moves continuously with the interest rate. This file discharges it.

Aggregation turns out not to depend on the rate at all -- the asset coordinate is the asset
coordinate whatever the rate, and `aggregateCapital` is equal across rates by `rfl` -- so all
the rate dependence sits in the stationary distribution, and `tendsto_stationary` supplies it.
Capital supply is then a continuous function composed with a convergent selection.

The family is indexed by the CLAMPED rate, so that a household problem is defined at every
real number while agreeing with the intended one on `[rlo, rhi]`. Without that the family
would need a proof of `0 < 1 + r` at every real `r`, which is false.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
-- Continuity in the rate is read off the augmented state space, which is built at a zero
-- borrowing limit; see `IncomeFluctuationAugmented`.
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap) {rlo rhi : ℝ}

/-- The household problem at the clamped rate, defined at every real number. -/
noncomputable def rateFamily (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) (r : ℝ) :
    IncomeFluctuation Z (0 : ℝ) assetCap :=
  P.withRate (clampRate rlo rhi r) (rateOK_of_floor_zero (one_add_clampRate_pos hrlo hle r))

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem rateFamily_eq (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi) {r : ℝ} (hr : r ∈ Icc rlo rhi)
    (hrr : P.RateOK r) : P.rateFamily hrlo hle r = P.withRate r hrr := by
  unfold rateFamily
  congr 1
  exact clampRate_eq hr

/-- **Capital supply is continuous in the interest rate.** -/
theorem continuousOn_capitalSupply (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r))
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r) :
    ContinuousOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
  intro r₀ hr₀
  have hrr₀ : P.RateOK r₀ := rateOK_of_floor_zero (by have := hr₀.1; linarith)
  exact (P.continuous_aggregateCapital.tendsto (ν r₀)).comp
    (P.tendsto_stationary hrlo hle hr₀ hrr₀ ν hν (huniq r₀ hr₀ hrr₀))

/-- **An Aiyagari stationary equilibrium exists**, with nothing assumed about the household
side beyond a selection of stationary distributions that is unique at each rate.

Compared with `exists_aiyagari_equilibrium`, the continuity of capital supply is no longer a
hypothesis: it is proved, from continuity of the policy in the rate and weak continuity of
aggregation. What remains assumed is the firm side -- any continuous demand schedule -- and
that excess demand changes sign, which is where the economics of the calibration enters. -/
theorem exists_equilibrium_of_selection (hrlo : 0 < 1 + rlo) (hle : rlo ≤ rhi)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r))
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r)
    (D : ℝ → ℝ) (hD : ContinuousOn D (Icc rlo rhi))
    (hlo : P.aggregateCapital (ν rlo) ≤ D rlo)
    (hhi : D rhi ≤ P.aggregateCapital (ν rhi)) :
    ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium (P.rateFamily hrlo hle) D r := by
  classical
  set S : ℝ → ℝ := fun r => P.aggregateCapital (ν (clampRate rlo rhi r)) with hS
  have hlo' : rlo ∈ Icc rlo rhi := ⟨le_rfl, hle⟩
  have hhi' : rhi ∈ Icc rlo rhi := ⟨hle, le_rfl⟩
  -- on the interval the clamp is inactive, so `S` is the supply schedule
  have hSeq : ∀ r ∈ Icc rlo rhi, S r = P.aggregateCapital (ν r) := fun r hr => by
    rw [hS]; simp only [clampRate_eq hr]
  refine exists_aiyagari_equilibrium (Pf := P.rateFamily hrlo hle) (S := S) hle ?_ ?_ hD
    (by rw [hSeq rlo hlo']; exact hlo) (by rw [hSeq rhi hhi']; exact hhi)
  · -- a stationary distribution realising `S` at every rate
    intro r
    refine ⟨ν (clampRate rlo rhi r), ?_, rfl⟩
    have hmem := clampRate_mem hle r
    have hrr : P.RateOK (clampRate rlo rhi r) :=
      rateOK_of_floor_zero (one_add_clampRate_pos hrlo hle r)
    have := hν _ hmem hrr
    rwa [show P.rateFamily hrlo hle r = P.withRate (clampRate rlo rhi r) hrr from rfl]
  · -- and `S` is continuous there
    refine (P.continuousOn_capitalSupply hrlo hle ν hν huniq).congr ?_
    exact fun r hr => hSeq r hr

end IncomeFluctuation

end LeanEconomics
