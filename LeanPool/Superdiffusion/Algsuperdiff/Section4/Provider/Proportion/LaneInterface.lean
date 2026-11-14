/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorDensity

/-!
# LaneInterface

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three-lane interface of the `§4.1` proportion assembly

ABK26, §4.1, `p.independence.between.scales`.  The proof of that proposition
splits `𝟙{𝒢(m; s, ε)ᶜ}` into the three constituent complements and applies each
lane's ratio lemma "with `θ` replaced by `θ/3`".  This module is the *interface*
of that step:

* `LaneTail M Ev θ c₁` — the common endpoint shape of one lane: at **every**
  window `{0,…,n}` the density of scales at which `Ev` fails exceeds `θ` with
  probability at most `exp(−c₁n)/3`.  It is exactly the conclusion shape the
  `𝒢₀` lane (`RatioTailClosed`) and the `𝒢₁` lane
  (`G1RatioTail`/`G1ThresholdArith`) deliver.
* `scaleProp_add_scaleProp_compl` — the complementarity
  `avsum 𝟙{𝒢} + avsum 𝟙{𝒢ᶜ} = 1` of the good and bad scale densities, which
  converts a bad-density endpoint into the frozen display's good form.

## References

* ABK26, `p.independence.between.scales`; `d.good.event.for.lambda`,
  (`e.lambda.good.events`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The common lane endpoint -/

/-- **The shape of one lane's ratio-tail endpoint.**  `LaneTail M Ev θ c₁` says
that for every window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not itself reach (covered inside the proved
`ratioTail_of_concentration`) — the density of scales at which `Ev` fails
exceeds `θ` with probability at most `exp(−c₁n)/3`.

The prefactor `1/3` is the union-bound share of the three-lane split: three
lanes at `exp(−c₁n)/3` recombine to `exp(−c₁n)`. -/
def LaneTail (M : ABKModel d) (Ev : ℤ → Set (Cutoff.CutoffSample d))
    (theta c1 : ℝ) : Prop :=
  ∀ n : ℕ,
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)

/-- A lane endpoint transfers to every larger level: the bad-density event
shrinks as the level rises. -/
theorem LaneTail.mono_level {M : ABKModel d} {Ev : ℤ → Set (Cutoff.CutoffSample d)}
    {theta theta' c1 : ℝ} (h : theta ≤ theta') (H : LaneTail M Ev theta c1) :
    LaneTail M Ev theta' c1 := by
  intro n
  refine le_trans (measure_mono ?_) (H n)
  intro omega homega
  exact lt_of_le_of_lt h homega

/-! ## 2. The good and bad scale densities -/

/-- **The good and bad scale densities are complementary.** -/
theorem scaleProp_add_scaleProp_compl {Omega : Type*} (Ev : ℤ → Set Omega) (n : ℕ)
    (omega : Omega) :
    scaleProp Ev n omega + scaleProp (fun m => (Ev m)ᶜ) n omega = 1 := by
  simp only [scaleProp]
  rw [← mul_add, ← Finset.sum_add_distrib]
  have key : (1 : ℝ) / ((n : ℝ) + 1) * (∑ _m ∈ Finset.Icc (0 : ℤ) (n : ℤ), (1 : ℝ)) = 1 := by
    rw [Finset.sum_const, Int.card_Icc]
    have h : ((n : ℤ) + 1 - 0).toNat = n + 1 := by omega
    rw [h]
    simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    field_simp
  refine Eq.trans ?_ key
  refine congrArg (fun z : ℝ => (1 : ℝ) / ((n : ℝ) + 1) * z) ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : omega ∈ Ev m
  · rw [ite_eq_left h, ite_eq_right (fun hc => hc h)]
    norm_num
  · rw [ite_eq_right h, ite_eq_left (show omega ∈ (Ev m)ᶜ from h)]
    norm_num

end

end Algsuperdiff.Section4.Provider.Proportion
