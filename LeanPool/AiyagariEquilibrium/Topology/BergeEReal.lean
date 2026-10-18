/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Topology.Berge
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Berge's maximum theorem for extended-real objectives

`LeanEconomics.Topology.Berge` proves the maximum theorem for a real-valued objective. Here
the objective may take the value `-∞`, which is what a reward like `log c` does at zero
consumption.

Allowing `-∞` is what lets a dynamic program be posed without a floor on the reward. Every
model in this library that uses a floor does so to keep the reward real-valued and bounded,
and then has to prove separately that the floor never binds. With an extended-real
objective the floor is unnecessary from the start.

## What changes, and what does not

Less than one might expect, and two of the changes make the proof *simpler*: `EReal` is a
complete lattice, so `le_sSup` and `sSup_le` carry no boundedness or nonemptiness side
conditions, unlike their conditionally-complete counterparts.

Upper semicontinuity here goes through *attainment* rather than interpolation: the supremum
over a nonempty compact set is achieved, so a strict bound at every point of the set is a
strict bound on the supremum. (`DenselyOrdered EReal` does exist in Mathlib, as
`instDenselyOrderedEReal`, so the interpolating proof would work too; the argmax half below
uses it.)

## Main results

* `LeanEconomics.continuous_maxValueE` : the maximum theorem for `EReal`-valued objectives.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y → EReal} {Γ : X → Set Y} {x : X} {c : EReal}

/-- The value of a maximisation problem whose objective may be `-∞`. No boundedness
hypothesis is needed: `EReal` is a complete lattice. -/
noncomputable def maxValueE (f : X → Y → EReal) (Γ : X → Set Y) (x : X) : EReal :=
  sSup (f x '' Γ x)

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem le_maxValueE {y : Y} (hy : y ∈ Γ x) : f x y ≤ maxValueE f Γ x := le_sSup ⟨y, hy, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem maxValueE_le (h : ∀ y ∈ Γ x, f x y ≤ c) : maxValueE f Γ x ≤ c :=
  sSup_le (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem continuous_fiberE (hf : Continuous ↿f) (x : X) : Continuous (f x) :=
  hf.comp (Continuous.prodMk_right x)

/-- The engine, exactly as in the real case: a strict upper bound over the constraint set
survives into a neighbourhood of the parameter. -/
theorem eventually_forall_ltE (hf : Continuous ↿f) (hΓc : IsCompact (Γ x))
    (huhc : UpperHemicontinuousAt Γ x) (hc : ∀ y ∈ Γ x, f x y < c) :
    ∀ᶠ x' in 𝓝 x, ∀ y ∈ Γ x', f x' y < c := by
  have hW : IsOpen (↿f ⁻¹' Iio c) := isOpen_Iio.preimage hf
  have hsub : ({x} : Set X) ×ˢ Γ x ⊆ ↿f ⁻¹' Iio c := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hc y hy
  obtain ⟨u, v, hu, hv, hxu, hΓv, huv⟩ := generalized_tube_lemma isCompact_singleton hΓc hW hsub
  filter_upwards [huhc.forall_isOpen v hv hΓv, hu.mem_nhds (hxu rfl)] with x' hΓ' hx'u
  intro y hy
  have hmem : (x', y) ∈ u ×ˢ v := ⟨hx'u, hΓ' hy⟩
  exact huv hmem

/-- Upper hemicontinuity of the constraint set gives upper semicontinuity of the value.
This goes through attainment of the supremum rather than interpolating a midpoint. -/
theorem upperSemicontinuousAt_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x) :
    UpperSemicontinuousAt (maxValueE f Γ) x := by
  intro c hc
  have h : ∀ y ∈ Γ x, f x y < c := fun y hy => lt_of_le_of_lt (le_maxValueE hy) hc
  filter_upwards [eventually_forall_ltE hf (hΓc x) huhc h] with x' hx'
  obtain ⟨y₀, hy₀, heq⟩ :=
    (hΓc x').exists_sSup_image_eq (hΓne x') (continuous_fiberE hf x').continuousOn
  rw [maxValueE, heq]
  exact hx' y₀ hy₀

/-- Lower hemicontinuity of the constraint set gives lower semicontinuity of the value. -/
theorem lowerSemicontinuousAt_maxValueE (hf : Continuous ↿f)
    (hlhc : LowerHemicontinuousAt Γ x) : LowerSemicontinuousAt (maxValueE f Γ) x := by
  intro c hc
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hy₀c⟩ := lt_sSup_iff.mp hc
  have hW : IsOpen (↿f ⁻¹' Ioi c) := isOpen_Ioi.preimage hf
  obtain ⟨u, v, hu, hv, hxu, hy₀v, huv⟩ := isOpen_prod_iff.mp hW x y₀ hy₀c
  filter_upwards [(lowerHemicontinuousAt_iff.mp hlhc) v hv ⟨y₀, hy₀, hy₀v⟩,
    hu.mem_nhds hxu] with x' hne hx'u
  obtain ⟨y, hyΓ, hyv⟩ := hne
  have hmem : (x', y) ∈ u ×ˢ v := ⟨hx'u, hyv⟩
  exact lt_of_lt_of_le (huv hmem) (le_maxValueE hyΓ)

/-- **Berge's maximum theorem for an extended-real objective.** -/
theorem continuousAt_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x)
    (hlhc : LowerHemicontinuousAt Γ x) : ContinuousAt (maxValueE f Γ) x := by
  rw [ContinuousAt, tendsto_order]
  exact ⟨lowerSemicontinuousAt_maxValueE hf hlhc,
    upperSemicontinuousAt_maxValueE hf hΓne hΓc huhc⟩

theorem continuous_maxValueE (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuous Γ) (hlhc : LowerHemicontinuous Γ) :
    Continuous (maxValueE f Γ) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_maxValueE hf hΓne hΓc (huhc x) (hlhc x)

/-- At a maximiser the objective equals the value, exactly as in the real case. -/
theorem maxValueE_eq (hf : Continuous ↿f) (hΓne : (Γ x).Nonempty) (hΓc : IsCompact (Γ x)) :
    ∃ y ∈ Γ x, maxValueE f Γ x = f x y := by
  obtain ⟨y₀, hy₀, heq⟩ := hΓc.exists_sSup_image_eq hΓne (continuous_fiberE hf x).continuousOn
  exact ⟨y₀, hy₀, heq⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- At a maximiser the objective equals the value. In `EReal` this needs no side
conditions, the order being complete. -/
theorem maxValueE_eq_of_mem_argmax {y : Y} (hy : y ∈ argmax f Γ x) :
    maxValueE f Γ x = f x y :=
  le_antisymm (maxValueE_le fun z hz => isMaxOn_iff.mp hy.2 z hz) (le_maxValueE hy.1)

/-- A maximiser exists. -/
theorem argmaxE_nonempty (hf : Continuous ↿f) (hΓne : (Γ x).Nonempty)
    (hΓc : IsCompact (Γ x)) : (argmax f Γ x).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := hΓc.exists_isMaxOn hΓne (continuous_fiberE hf x).continuousOn
  exact ⟨y, hy, hmax⟩

/-- **Berge's maximum theorem, the maximiser half, for an extended-real objective.** The
proof is the real one unchanged: away from an open set containing the maximisers the
objective is strictly below the value, that gap survives into a neighbourhood by the
engine, and lower semicontinuity of the value keeps the value above the gap. -/
theorem upperHemicontinuousAt_argmaxE (hf : Continuous ↿f)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x)
    (hlhc : LowerHemicontinuousAt Γ x) : UpperHemicontinuousAt (argmax f Γ) x := by
  apply UpperHemicontinuousAt.of_forall_isOpen
  intro V hV hsub
  by_cases hsubV : Γ x ⊆ V
  · filter_upwards [huhc.forall_isOpen V hV hsubV] with x' h
    exact fun y hy => h hy.1
  · obtain ⟨y', hy', hy'V⟩ := Set.not_subset.mp hsubV
    have hKc : IsCompact (Γ x ∩ Vᶜ) := (hΓc x).inter_right hV.isClosed_compl
    obtain ⟨y₁, hy₁, hmax₁⟩ :=
      hKc.exists_isMaxOn ⟨y', hy', hy'V⟩ (continuous_fiberE hf x).continuousOn
    have hlt : f x y₁ < maxValueE f Γ x := by
      rcases (le_maxValueE hy₁.1).lt_or_eq with h | h
      · exact h
      · refine absurd (hsub ⟨hy₁.1, isMaxOn_iff.mpr fun z hz => ?_⟩) hy₁.2
        rw [h]
        exact le_maxValueE hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hbound : ∀ y ∈ Γ x ∩ Vᶜ, f x y < c := fun y hy =>
      lt_of_le_of_lt (isMaxOn_iff.mp hmax₁ y hy) hc1
    filter_upwards [eventually_forall_ltE hf hKc (huhc.inter hV.isClosed_compl) hbound,
      lowerSemicontinuousAt_maxValueE hf hlhc c hc2] with x' h1 h2
    intro y hy
    by_contra hyV
    have hlt' : f x' y < c := h1 y ⟨hy.1, hyV⟩
    rw [← maxValueE_eq_of_mem_argmax hy] at hlt'
    exact absurd h2 (not_lt.mpr hlt'.le)

theorem upperHemicontinuous_argmaxE (hf : Continuous ↿f)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuous Γ) (hlhc : LowerHemicontinuous Γ) :
    UpperHemicontinuous (argmax f Γ) := fun x =>
  upperHemicontinuousAt_argmaxE hf hΓc (huhc x) (hlhc x)

end LeanEconomics
