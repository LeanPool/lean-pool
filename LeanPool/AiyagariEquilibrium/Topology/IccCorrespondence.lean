/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Instances.Real.Lemmas


/-!
# A closed interval with moving endpoints is a continuous correspondence

`x ↦ Set.Icc (f x) (g x)` is upper and lower hemicontinuous when `f` and `g` are
continuous. This is the hypothesis Berge's maximum theorem needs, and a budget set
`{a' | 0 ≤ a' ≤ m a}` is exactly of this shape, so these two lemmas are what let a
constrained consumption problem be posed as a dynamic program.

## Main results

* `LeanEconomics.upperHemicontinuous_Icc`
* `LeanEconomics.lowerHemicontinuous_Icc`

## The asymmetry in the hypotheses

Upper hemicontinuity needs no order hypothesis: where `g x < f x` the interval is empty,
and the empty set is contained in everything.

Lower hemicontinuity needs `f ≤ g` *everywhere*, not merely at the point in question, and
this is not a technicality. If `f x = g x` while `f x' > g x'` at nearby `x'`, then `Γ x`
is a single point and `Γ x'` is empty, so an open set meeting `Γ x` meets nothing nearby.
Lower hemicontinuity genuinely fails there. An interval that is allowed to collapse and
then vanish is not a continuous correspondence.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

variable {X : Type*} [TopologicalSpace X] {f g : X → ℝ}

/-- An interval with continuous endpoints is upper hemicontinuous. -/
theorem upperHemicontinuous_Icc (hf : Continuous f) (hg : Continuous g) :
    UpperHemicontinuous fun x => Set.Icc (f x) (g x) := by
  apply UpperHemicontinuous.of_forall_isOpen
  intro x V hV hsub
  rcases le_or_gt (f x) (g x) with hle | hlt
  · -- The interval is nonempty: thicken it slightly and stay inside `V`.
    obtain ⟨ε, hε, hthick⟩ := isCompact_Icc.exists_thickening_subset_open hV hsub
    have h1 : ∀ᶠ x' in 𝓝 x, |f x' - f x| < ε / 2 := by
      simpa [Real.dist_eq] using Metric.tendsto_nhds.mp (hf.tendsto x) (ε / 2) (by positivity)
    have h2 : ∀ᶠ x' in 𝓝 x, |g x' - g x| < ε / 2 := by
      simpa [Real.dist_eq] using Metric.tendsto_nhds.mp (hg.tendsto x) (ε / 2) (by positivity)
    filter_upwards [h1, h2] with x' hx1 hx2
    intro z hz
    obtain ⟨hf1, hf2⟩ := abs_lt.mp hx1
    obtain ⟨hg1, hg2⟩ := abs_lt.mp hx2
    obtain ⟨hzl, hzu⟩ := hz
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨max (f x) (min (g x) z), ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩, ?_⟩
    rw [Real.dist_eq]
    rcases le_total z (f x) with h | h
    · rw [min_eq_right (h.trans hle), max_eq_left h, abs_lt]
      constructor <;> linarith
    · rcases le_total z (g x) with h' | h'
      · rw [min_eq_right h', max_eq_right h, sub_self, abs_zero]
        exact hε
      · rw [min_eq_left h', max_eq_right hle, abs_lt]
        constructor <;> linarith
  · -- The interval is empty, and stays empty nearby.
    have hev : ∀ᶠ x' in 𝓝 x, g x' < f x' :=
      hg.continuousAt.eventually_lt hf.continuousAt hlt
    filter_upwards [hev] with x' h
    rw [Set.Icc_eq_empty_of_lt h]
    exact Set.empty_subset V

/-- An interval with continuous endpoints that never collapses past emptiness is lower
hemicontinuous. -/
theorem lowerHemicontinuous_Icc (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ x, f x ≤ g x) : LowerHemicontinuous fun x => Set.Icc (f x) (g x) := by
  refine lowerHemicontinuous_iff.mpr fun x => lowerHemicontinuousAt_iff.mpr ?_
  intro V hV hne
  obtain ⟨z, hzI, hzV⟩ := hne
  -- Clamp `z` into the interval at each nearby point; the clamp is continuous and fixes
  -- `z` at `x`, so it stays inside `V` nearby and witnesses the intersection.
  have hw : Continuous fun x' => max (f x') (min (g x') z) :=
    hf.max (hg.min continuous_const)
  have hwx : max (f x) (min (g x) z) = z := by
    rw [min_eq_right hzI.2, max_eq_right hzI.1]
  have hev : ∀ᶠ x' in 𝓝 x, max (f x') (min (g x') z) ∈ V := by
    have h := (hw.tendsto x) (hV.mem_nhds (by rw [hwx]; exact hzV))
    exact h
  filter_upwards [hev] with x' hx'
  exact ⟨_, ⟨le_max_left _ _, max_le (hle x') (min_le_left _ _)⟩, hx'⟩

end LeanEconomics
