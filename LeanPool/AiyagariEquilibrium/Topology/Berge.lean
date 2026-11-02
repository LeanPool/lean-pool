/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Berge's maximum theorem

Consider maximising a continuous objective `f x y` over a constraint set `Γ x` that moves
with the parameter `x`. Berge's maximum theorem says that if `Γ` is continuous -- upper and
lower hemicontinuous -- with nonempty compact values, then the value of the problem varies
continuously with `x`, and the set of maximisers varies upper hemicontinuously.

The two halves need the two halves of the continuity of `Γ`, and it is worth keeping track
of which: upper hemicontinuity gives upper semicontinuity of the value, lower
hemicontinuity gives lower semicontinuity of it. Neither alone suffices.

Mathlib supplies the hemicontinuity definitions (`UpperHemicontinuousAt`,
`LowerHemicontinuousAt`) but not this theorem.

## Main definitions

* `LeanEconomics.maxValue f Γ x` : the value `sSup (f x '' Γ x)` of the problem at `x`.
* `LeanEconomics.argmax f Γ x` : the set of maximisers at `x`.

## Main results

* `LeanEconomics.continuousAt_maxValue` : **the maximum theorem** -- the value function is
  continuous.
* `LeanEconomics.upperHemicontinuousAt_argmax` : the maximiser correspondence is upper
  hemicontinuous.
* `LeanEconomics.argmax_nonempty`, `LeanEconomics.isCompact_argmax` : it has nonempty
  compact values.

## A check on the hypotheses

Berge's hypotheses are strong enough to be worth checking they can all hold at once:
`continuous_maxValue_const` instantiates them at a constraint set that does not move with
the parameter. Without such a witness the theorems above could be vacuous.

## Implementation notes

`eventually_forall_lt` is the engine. It says that a strict bound on `f` over `Γ x`
persists into a neighbourhood of `x`, and it is proved from the generalized tube lemma
together with upper hemicontinuity. Upper semicontinuity of the value follows at once, and
so does the hard half of upper hemicontinuity of `argmax`, applied there to the
correspondence `x ↦ Γ x ∩ Vᶜ`. Stating it without reference to a supremum is what lets it
serve the second purpose, where that correspondence may take empty values.

## References

* Berge, *Espaces topologiques: Fonctions multivoques*, 1959.
* Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y → ℝ} {Γ : X → Set Y} {x : X} {c : ℝ}

/-- The value of the problem `max f x y` subject to `y ∈ Γ x`. -/
noncomputable def maxValue (f : X → Y → ℝ) (Γ : X → Set Y) (x : X) : ℝ := sSup (f x '' Γ x)

/-- The set of maximisers of `f x` over `Γ x`. The codomain is any preorder, so that the
same definition serves the extended-real objectives of
`LeanEconomics.Topology.BergeEReal`. -/
def argmax {Z : Type*} [Preorder Z] (f : X → Y → Z) (Γ : X → Set Y) (x : X) : Set Y :=
  {y ∈ Γ x | IsMaxOn (f x) (Γ x) y}

/-- The objective as a function of the choice alone, with the parameter fixed. -/
theorem continuous_fiber (hf : Continuous ↿f) (x : X) : Continuous (f x) :=
  hf.comp (Continuous.prodMk_right x)

theorem bddAbove_image (hf : Continuous ↿f) (hΓc : IsCompact (Γ x)) :
    BddAbove (f x '' Γ x) :=
  hΓc.bddAbove_image (continuous_fiber hf x).continuousOn

theorem le_maxValue (hf : Continuous ↿f) (hΓc : IsCompact (Γ x)) {y : Y} (hy : y ∈ Γ x) :
    f x y ≤ maxValue f Γ x :=
  le_csSup (bddAbove_image hf hΓc) ⟨y, hy, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem maxValue_le (hΓne : (Γ x).Nonempty) (h : ∀ y ∈ Γ x, f x y ≤ c) :
    maxValue f Γ x ≤ c :=
  csSup_le (hΓne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

/-- **The engine.** A strict upper bound on the objective over the constraint set survives
into a neighbourhood of the parameter. This is the generalized tube lemma combined with
upper hemicontinuity, and it makes no nonemptiness assumption, which matters because it is
applied below to a correspondence that may be empty-valued. -/
theorem eventually_forall_lt (hf : Continuous ↿f) (hΓc : IsCompact (Γ x))
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

/-- Upper hemicontinuity of the constraint set gives upper semicontinuity of the value. -/
theorem upperSemicontinuousAt_maxValue (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x) :
    UpperSemicontinuousAt (maxValue f Γ) x := by
  intro c hc
  obtain ⟨c', hc1, hc2⟩ := exists_between hc
  have h : ∀ y ∈ Γ x, f x y < c' := fun y hy => lt_of_le_of_lt (le_maxValue hf (hΓc x) hy) hc1
  filter_upwards [eventually_forall_lt hf (hΓc x) huhc h] with x' hx'
  exact lt_of_le_of_lt (maxValue_le (hΓne x') fun y hy => (hx' y hy).le) hc2

/-- Lower hemicontinuity of the constraint set gives lower semicontinuity of the value. -/
theorem lowerSemicontinuousAt_maxValue (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (hlhc : LowerHemicontinuousAt Γ x) :
    LowerSemicontinuousAt (maxValue f Γ) x := by
  intro c hc
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hy₀c⟩ := exists_lt_of_lt_csSup ((hΓne x).image _) hc
  have hW : IsOpen (↿f ⁻¹' Ioi c) := isOpen_Ioi.preimage hf
  obtain ⟨u, v, hu, hv, hxu, hy₀v, huv⟩ := isOpen_prod_iff.mp hW x y₀ hy₀c
  filter_upwards [(lowerHemicontinuousAt_iff.mp hlhc) v hv ⟨y₀, hy₀, hy₀v⟩,
    hu.mem_nhds hxu] with x' hne hx'u
  obtain ⟨y, hyΓ, hyv⟩ := hne
  have hmem : (x', y) ∈ u ×ˢ v := ⟨hx'u, hyv⟩
  exact lt_of_lt_of_le (huv hmem) (le_maxValue hf (hΓc x') hyΓ)

/-- **Berge's maximum theorem**, the value function half: if the constraint correspondence
is continuous with nonempty compact values and the objective is continuous, then the value
of the problem is continuous in the parameter. -/
theorem continuousAt_maxValue (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x)
    (hlhc : LowerHemicontinuousAt Γ x) : ContinuousAt (maxValue f Γ) x := by
  rw [ContinuousAt, tendsto_order]
  exact ⟨lowerSemicontinuousAt_maxValue hf hΓne hΓc hlhc,
    upperSemicontinuousAt_maxValue hf hΓne hΓc huhc⟩

/-- The value function is continuous, given continuity of the correspondence everywhere. -/
theorem continuous_maxValue (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuous Γ) (hlhc : LowerHemicontinuous Γ) :
    Continuous (maxValue f Γ) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_maxValue hf hΓne hΓc (huhc x) (hlhc x)

/-- A maximiser exists: the constraint set is compact and the objective continuous. -/
theorem argmax_nonempty (hf : Continuous ↿f) (hΓne : (Γ x).Nonempty) (hΓc : IsCompact (Γ x)) :
    (argmax f Γ x).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := hΓc.exists_isMaxOn hΓne (continuous_fiber hf x).continuousOn
  exact ⟨y, hy, hmax⟩

theorem isCompact_argmax (hf : Continuous ↿f) (hΓc : IsCompact (Γ x)) :
    IsCompact (argmax f Γ x) := by
  have hcl : IsClosed {y | IsMaxOn (f x) (Γ x) y} := by
    have heq : {y | IsMaxOn (f x) (Γ x) y} = ⋂ z ∈ Γ x, {y | f x z ≤ f x y} := by
      ext y; simp [isMaxOn_iff]
    rw [heq]
    exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_fiber hf x)
  exact hΓc.inter_right hcl

/-- At a maximiser the objective equals the value of the problem. -/
theorem maxValue_eq (hf : Continuous ↿f) (hΓc : IsCompact (Γ x)) {y : Y}
    (hy : y ∈ argmax f Γ x) : maxValue f Γ x = f x y :=
  le_antisymm (maxValue_le ⟨y, hy.1⟩ fun z hz => isMaxOn_iff.mp hy.2 z hz)
    (le_maxValue hf hΓc hy.1)

/-- **Berge's maximum theorem**, the maximiser half: the set of maximisers is upper
hemicontinuous. It need not be lower hemicontinuous -- a maximiser can appear abruptly when
a tie is reached -- which is why the conclusion is one-sided. -/
theorem upperHemicontinuousAt_argmax (hf : Continuous ↿f) (hΓne : ∀ x, (Γ x).Nonempty)
    (hΓc : ∀ x, IsCompact (Γ x)) (huhc : UpperHemicontinuousAt Γ x)
    (hlhc : LowerHemicontinuousAt Γ x) : UpperHemicontinuousAt (argmax f Γ) x := by
  apply UpperHemicontinuousAt.of_forall_isOpen
  intro V hV hsub
  by_cases hsubV : Γ x ⊆ V
  · -- Nothing to do: the whole constraint set is eventually inside `V`.
    filter_upwards [huhc.forall_isOpen V hV hsubV] with x' h
    exact fun y hy => h hy.1
  · -- The part of the constraint set outside `V` is compact, nonempty, and strictly
    -- suboptimal; both facts persist into a neighbourhood of `x`.
    obtain ⟨y', hy', hy'V⟩ := Set.not_subset.mp hsubV
    have hKc : IsCompact (Γ x ∩ Vᶜ) := (hΓc x).inter_right hV.isClosed_compl
    obtain ⟨y₁, hy₁, hmax₁⟩ :=
      hKc.exists_isMaxOn ⟨y', hy', hy'V⟩ (continuous_fiber hf x).continuousOn
    have hlt : f x y₁ < maxValue f Γ x := by
      rcases (le_maxValue hf (hΓc x) hy₁.1).lt_or_eq with h | h
      · exact h
      · refine absurd (hsub ⟨hy₁.1, isMaxOn_iff.mpr fun z hz => ?_⟩) hy₁.2
        rw [h]
        exact le_maxValue hf (hΓc x) hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hbound : ∀ y ∈ Γ x ∩ Vᶜ, f x y < c := fun y hy =>
      lt_of_le_of_lt (isMaxOn_iff.mp hmax₁ y hy) hc1
    filter_upwards [eventually_forall_lt hf hKc (huhc.inter hV.isClosed_compl) hbound,
      lowerSemicontinuousAt_maxValue hf hΓne hΓc hlhc c hc2] with x' h1 h2
    intro y hy
    by_contra hyV
    have hlt' : f x' y < c := h1 y ⟨hy.1, hyV⟩
    rw [← maxValue_eq hf (hΓc x') hy] at hlt'
    exact absurd h2 (not_lt.mpr hlt'.le)

/-- **A single-valued upper hemicontinuous correspondence is a continuous function.** This
is how the second half of Berge becomes a continuity statement about the optimal policy,
once the maximiser is known to be unique. -/
theorem continuous_of_upperHemicontinuous_singleton {Γ : X → Set Y} {g : X → Y}
    (huhc : UpperHemicontinuous Γ) (hsingle : ∀ x, Γ x = {g x}) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_nhds]
  intro V hV hgx
  have hsub : Γ x ⊆ V := by
    rw [hsingle x]
    simpa using hgx
  filter_upwards [huhc.forall_isOpen x V hV hsub] with x' h
  refine h ?_
  rw [hsingle x']
  rfl

/-- The same, on a set: single-valuedness is only needed where the conclusion is wanted.
This is the version the household models need, since the optimal action is unique on the
region where the value function is concave, not necessarily everywhere. -/
theorem continuousOn_of_upperHemicontinuous_singleton {Γ : X → Set Y} {g : X → Y} {s : Set X}
    (huhc : UpperHemicontinuous Γ) (hsingle : ∀ x ∈ s, Γ x = {g x}) : ContinuousOn g s := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_nhds]
  intro V hV hgx
  have hsub : Γ x ⊆ V := by
    rw [hsingle x hx]
    simpa using hgx
  filter_upwards [nhdsWithin_le_nhds (huhc.forall_isOpen x V hV hsub), self_mem_nhdsWithin]
    with x' h hx'
  refine h ?_
  rw [hsingle x' hx']
  rfl

/-! ### A constraint set that does not move

The degenerate case, recorded to show the hypotheses of the theorems above are
simultaneously satisfiable. -/

section Constant

variable (K : Set Y)

theorem upperHemicontinuous_const : UpperHemicontinuous (fun _ : X => K) :=
  UpperHemicontinuous.of_forall_isOpen fun _ _ _ h => Eventually.of_forall fun _ => h

theorem lowerHemicontinuous_const : LowerHemicontinuous (fun _ : X => K) :=
  lowerHemicontinuous_iff.mpr fun _ =>
    lowerHemicontinuousAt_iff.mpr fun _ _ h => Eventually.of_forall fun _ => h

/-- **Berge is not vacuous.** With a fixed compact nonempty constraint set every hypothesis
of the maximum theorem holds, and the value of the problem is continuous in the
parameter. -/
theorem continuous_maxValue_const (hf : Continuous ↿f) (hKne : K.Nonempty) (hKc : IsCompact K) :
    Continuous (maxValue f fun _ : X => K) :=
  continuous_maxValue hf (fun _ => hKne) (fun _ => hKc)
    (upperHemicontinuous_const K) (lowerHemicontinuous_const K)

end Constant

end LeanEconomics
