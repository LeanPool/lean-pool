/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolPartition
import Mathlib.Tactic.NormNum

/-!
# Pointwise bounded Borel representatives

`L²` bounds are naturally almost everywhere statements.  Clipping the chosen
measurable representative into `[0,1]` gives an everywhere bounded Borel
function representing the same `L²` vector.  The clipped high and low sets
have the same measures and asymptotic properties as the sets constructed in
`PoolPartition`.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open Filter MeasureTheory Set Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An everywhere `[0,1]`-valued representative of an almost everywhere bounded
weak limit. -/
def clippedRepresentative (g : Lp ℝ 2 μ) (x : Ω) : ℝ :=
  min 1 (max 0 (g x))

theorem measurable_clippedRepresentative (g : Lp ℝ 2 μ) :
    Measurable (clippedRepresentative g) :=
  measurable_const.min (measurable_const.max (Lp.stronglyMeasurable g).measurable)

theorem clippedRepresentative_bounds (g : Lp ℝ 2 μ) (x : Ω) :
    0 ≤ clippedRepresentative g x ∧ clippedRepresentative g x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem clippedRepresentative_ae_eq (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    clippedRepresentative g =ᵐ[μ] g := by
  filter_upwards [hg0, hg1] with x hx0 hx1
  simp only [clippedRepresentative, max_eq_right hx0, min_eq_right hx1]

theorem memLp_clippedRepresentative (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    MemLp (clippedRepresentative g) 2 μ :=
  (memLp_congr_ae (clippedRepresentative_ae_eq g hg0 hg1)).mpr (Lp.memLp g)

theorem clippedRepresentative_toLp (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    (memLp_clippedRepresentative g hg0 hg1).toLp (clippedRepresentative g) = g := by
  exact Lp.ext ((memLp_clippedRepresentative g hg0 hg1).coeFn_toLp.trans
    (clippedRepresentative_ae_eq g hg0 hg1))

/-- The fixed high set defined from the everywhere bounded representative. -/
def clippedHighSet (g : Lp ℝ 2 μ) : Set Ω := {x | clippedRepresentative g x = 1}

/-- The complementary fixed low set. -/
def clippedLowSet (g : Lp ℝ 2 μ) : Set Ω := (clippedHighSet g)ᶜ

/-- The near-one part of the clipped low set. -/
def clippedNearOneLowSet (g : Lp ℝ 2 μ) (δ : ℝ) : Set Ω :=
  clippedLowSet g ∩ {x | 1 - δ ≤ clippedRepresentative g x}

theorem measurableSet_clippedHighSet (g : Lp ℝ 2 μ) :
    MeasurableSet (clippedHighSet g) :=
  measurableSet_eq_fun (measurable_clippedRepresentative g) measurable_const

theorem measurableSet_clippedLowSet (g : Lp ℝ 2 μ) :
    MeasurableSet (clippedLowSet g) :=
  (measurableSet_clippedHighSet g).compl

theorem measurableSet_clippedNearOneLowSet (g : Lp ℝ 2 μ) (δ : ℝ) :
    MeasurableSet (clippedNearOneLowSet g δ) :=
  (measurableSet_clippedLowSet g).inter
    (measurableSet_le measurable_const (measurable_clippedRepresentative g))

theorem clippedRepresentative_lt_one_on_low (g : Lp ℝ 2 μ) {x : Ω}
    (hx : x ∈ clippedLowSet g) : clippedRepresentative g x < 1 := by
  exact lt_of_le_of_ne (clippedRepresentative_bounds g x).2 hx

theorem disjoint_clippedHighSet_clippedLowSet (g : Lp ℝ 2 μ) :
    Disjoint (clippedHighSet g) (clippedLowSet g) := disjoint_compl_right

theorem clippedHighSet_union_clippedLowSet (g : Lp ℝ 2 μ) :
    clippedHighSet g ∪ clippedLowSet g = univ := union_compl_self _

theorem clippedHighSet_ae_eq (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    clippedHighSet g =ᵐ[μ] highSet g := by
  filter_upwards [clippedRepresentative_ae_eq g hg0 hg1] with x hx
  simp only [clippedHighSet, highSet, mem_ofPred_eq, hx]

theorem clippedNearOneLowSet_ae_eq (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) (δ : ℝ) :
    clippedNearOneLowSet g δ =ᵐ[μ] nearOneLowSet g δ := by
  filter_upwards [clippedRepresentative_ae_eq g hg0 hg1] with x hx
  simp only [clippedNearOneLowSet, nearOneLowSet, clippedLowSet, lowSet,
    clippedHighSet, highSet, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, hx]

theorem measureReal_clippedNearOneLowSet (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) (δ : ℝ) :
    μ.real (clippedNearOneLowSet g δ) = μ.real (nearOneLowSet g δ) :=
  measureReal_congr (clippedNearOneLowSet_ae_eq g hg0 hg1 δ)

theorem setIntegral_clippedHighSet (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    ∫ x in clippedHighSet g, g x ∂μ = μ.real (clippedHighSet g) := by
  calc
    ∫ x in clippedHighSet g, g x ∂μ =
        ∫ x in clippedHighSet g, clippedRepresentative g x ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (clippedRepresentative_ae_eq g hg0 hg1).symm)
    _ = ∫ _ in clippedHighSet g, (1 : ℝ) ∂μ :=
      setIntegral_congr_fun (measurableSet_clippedHighSet g) fun _ hx => hx
    _ = μ.real (clippedHighSet g) := by simp

variable [IsFiniteMeasure μ]

theorem clipped_high_miss_tendsto_zero (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) {g : Lp ℝ 2 μ}
    (hu : WeaklyConverges
      (fun n => indicatorConstLp 2 (hA n) (measure_ne_top μ (A n)) (1 : ℝ)) g)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    Tendsto (fun n => μ.real (clippedHighSet g \ A n)) atTop (𝓝 0) := by
  have heq (n : ℕ) : μ.real (clippedHighSet g \ A n) = μ.real (highSet g \ A n) :=
    measureReal_congr ((clippedHighSet_ae_eq g hg0 hg1).diff EventuallyEqSet.rfl)
  simpa only [heq] using high_miss_tendsto_zero A hA hu

theorem tendsto_measureReal_clippedNearOneLowSet (g : Lp ℝ 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂μ, g x ≤ 1) :
    Tendsto (fun n : ℕ => μ.real (clippedNearOneLowSet g ((1 / 2 : ℝ) ^ n)))
      atTop (𝓝 0) := by
  simpa only [measureReal_clippedNearOneLowSet g hg0 hg1] using
    tendsto_measureReal_nearOneLowSet g hg1

theorem exists_rational_clipped_low_margin (g : ℕ → Lp ℝ 2 μ)
    (hg0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ g i x) (hg1 : ∀ i, ∀ᵐ x ∂μ, g i x ≤ 1)
    (ℓ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ i < ℓ, μ.real (clippedNearOneLowSet (g i) (2 * (τ : ℝ))) < η := by
  simpa only [measureReal_clippedNearOneLowSet (g _) (hg0 _) (hg1 _)] using
    exists_rational_low_margin g hg1 ℓ hη

end Klr.Pool
