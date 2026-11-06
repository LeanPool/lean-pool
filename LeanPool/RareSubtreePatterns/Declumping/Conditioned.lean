/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Declumping.Probability
public import LeanPool.RareSubtreePatterns.Bienayme.Conditioned

/-!
# Lemma `lem:declump_to_raw` for size-conditioned Bienaymé trees

Source lines 2343–2401. The abstract reduction `PlaneTree.declump_to_raw` assumes that every
law in the family is a probability measure. Here we only require this eventually along the
limit filter (`declump_to_raw_of_eventually`), and specialize to the family
`n ↦ 𝒯^n = conditioned μ n` along the filter `admissibleAtTop μ` of large admissible sizes,
where the conditioned laws are probability measures (`conditioned_declump_to_raw`).
Measurability of counts is automatic for the discrete σ-algebra on finite plane trees.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace PoissonDeclumping.PlaneTree

/-- Lemma `lem:declump_to_raw` for laws that are only *eventually* probability measures,
on an arbitrary measurable structure on trees (with measurable declumped counts). -/
theorem declump_to_raw_of_eventually_of_measurable {mT : MeasurableSpace PlaneTree}
    {ι : Type*} (l : Filter ι) (μ : ι → Measure PlaneTree)
    (hμ : ∀ᶠ i in l, IsProbabilityMeasure (μ i)) (B : Set ℕ) (G : ι → PlaneTree → Prop)
    (rate : ι → ℝ≥0)
    (hprop : ∀ i, PropagatesOutside B (G i))
    (hmeas : ∀ i, Measurable (markCount (declumpedMark B (G i))))
    (hroot : Tendsto (fun i => (μ i).real {T | G i T}) l (𝓝 0))
    (htv : Tendsto (fun i => paperTVDist
      ((μ i).map (markCount (declumpedMark B (G i)))) (poissonMeasure (rate i)))
      l (𝓝 0)) :
    Tendsto (fun i => (μ i).real {T | markCount (G i) T = 0} -
      Real.exp (-(rate i : ℝ))) l (𝓝 0) := by
  refine squeeze_zero_norm'
    (a := fun i => (μ i).real {T | G i T} + paperTVDist
      ((μ i).map (markCount (declumpedMark B (G i)))) (poissonMeasure (rate i)))
    (hμ.mono fun i hi => ?_) ?_
  · simpa only [Real.norm_eq_abs] using
      raw_zero_poisson_error_le (μ i) (rate i) (hprop i) (hmeas i)
  · simpa only [zero_add] using hroot.add htv

/-- Lemma `lem:declump_to_raw` for laws on finite plane trees (discrete σ-algebra) that are
eventually probability measures along the filter `l`. -/
theorem declump_to_raw_of_eventually {ι : Type*} (l : Filter ι) (μ : ι → Measure PlaneTree)
    (hμ : ∀ᶠ i in l, IsProbabilityMeasure (μ i)) (B : Set ℕ) (G : ι → PlaneTree → Prop)
    (rate : ι → ℝ≥0)
    (hprop : ∀ i, PropagatesOutside B (G i))
    (hroot : Tendsto (fun i => (μ i).real {T | G i T}) l (𝓝 0))
    (htv : Tendsto (fun i => paperTVDist
      ((μ i).map (markCount (declumpedMark B (G i)))) (poissonMeasure (rate i)))
      l (𝓝 0)) :
    Tendsto (fun i => (μ i).real {T | markCount (G i) T = 0} -
      Real.exp (-(rate i : ℝ))) l (𝓝 0) :=
  declump_to_raw_of_eventually_of_measurable l μ hμ B G rate hprop
    (fun _ => Measurable.of_discrete) hroot htv

/-- **Lemma `lem:declump_to_raw`** (source lines 2343–2357) for the size-conditioned
Bienaymé trees `𝒯^n`, as `n → ∞` along admissible sizes: if the marks `G_n` (the paper's
`G_{k_n}`) propagate to parents of degree outside `B`, `𝐏(G_n(𝒯^n)) → 0`, and the declumped
count `N̂_n(𝒯^n)` is close in total variation to `Po(λ_n)`, then
`𝐏(N_n(𝒯^n) = 0) - e^{-λ_n} → 0`.

The size `n` itself is the index. The statement holds for every offspring law `μ`; for the
paper's critical `μ` with `μ_1 ≠ 1` the filter `admissibleAtTop μ` is proper
(`admissibleAtTop_neBot`), so the limit statement is not vacuous. -/
theorem conditioned_declump_to_raw (μ : PMF ℕ) (B : Set ℕ) (G : ℕ → PlaneTree → Prop)
    (rate : ℕ → ℝ≥0)
    (hprop : ∀ n, PropagatesOutside B (G n))
    (hroot : Tendsto (fun n => (conditioned μ n).real {T | G n T}) (admissibleAtTop μ) (𝓝 0))
    (htv : Tendsto (fun n => paperTVDist
      ((conditioned μ n).map (markCount (declumpedMark B (G n)))) (poissonMeasure (rate n)))
      (admissibleAtTop μ) (𝓝 0)) :
    Tendsto (fun n => (conditioned μ n).real {T | markCount (G n) T = 0} -
      Real.exp (-(rate n : ℝ))) (admissibleAtTop μ) (𝓝 0) :=
  declump_to_raw_of_eventually (admissibleAtTop μ) (conditioned μ)
    (eventually_isProbabilityMeasure_conditioned μ) B G rate hprop hroot htv

end PoissonDeclumping.PlaneTree
