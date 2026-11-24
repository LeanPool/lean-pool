/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ImageGermCover
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Selecting a side of a parameter over an image limit

For the restriction step of XII (2.1), pages 243--244, a subcurve
approaching a vertex through a corner makes that corner accumulate
in the original curve image. A closed parameter period is compact,
so this accumulation lifts to a parameter over the vertex. A nearby
parameter different from it lies on one of its two sides. This
selects one of the original incoming or outgoing region germs.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- Lift image accumulation to a parameter in a prescribed compact
real interval. The lifted parameter is a limit of parameters whose
images lie in the chosen set. -/
theorem exists_period_parameter_in_closure_preimage
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {f : ℝ → S} (hf : Continuous f) {a b : ℝ} {v : S} {B : Set S}
    (hv : v ∈ closure (f '' Icc a b ∩ B)) :
    ∃ s ∈ Icc a b, f s = v ∧ s ∈ closure (Icc a b ∩ f ⁻¹' B) := by
  let A := Icc a b
  let : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_Icc
  let g : A → S := fun t => f t.val
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hgrange : range g = f '' Icc a b := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.val, s.property, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  obtain ⟨s, hgs, hscl⟩ := exists_fibre_point_in_closure_preimage hg (hgrange.symm ▸ hv)
  refine ⟨s.val, s.property, hgs, ?_⟩
  have hval := image_closure_subset_closure_image
    (f := (Subtype.val : A → ℝ)) continuous_subtype_val ⟨s, hscl, rfl⟩
  apply closure_mono (t := Icc a b ∩ f ⁻¹' B) _ hval
  rintro z ⟨t, ht, rfl⟩
  exact ⟨t.property, ht⟩

/-- Accumulation at a parameter whose image is outside `B` selects
a nearby parameter on one of its two sides. The side hypotheses
can be the two recorded sector germs of a trace. -/
theorem exists_side_meeting_of_closure_preimage
    {S : Type*} {f : ℝ → S} {C : Set ℝ} {B L R : Set S}
    {s ε : ℝ} (hε : 0 < ε) (hfs : f s ∉ B)
    (hs : s ∈ closure (C ∩ f ⁻¹' B))
    (hL : ∀ t ∈ C, t ∈ Ioo (s - ε) s → f t ∈ L)
    (hR : ∀ t ∈ C, t ∈ Ioo s (s + ε) → f t ∈ R) :
    (B ∩ L).Nonempty ∨ (B ∩ R).Nonempty := by
  obtain ⟨t, htN, htC, htB⟩ := mem_closure_iff.mp hs (Ioo (s - ε) (s + ε))
    isOpen_Ioo ⟨by linarith, by linarith⟩
  have hts : t ≠ s := fun heq => hfs (heq ▸ htB)
  rcases lt_or_gt_of_ne hts with hlt | hgt
  · exact Or.inl ⟨f t, htB, hL t htC ⟨htN.1, hlt⟩⟩
  · exact Or.inr ⟨f t, htB, hR t htC ⟨hgt, htN.2⟩⟩

/-- Apply compact-period selection to a continuous approach whose
image lies in the original period and in a chosen corner. -/
theorem exists_period_parameter_of_approach
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a b c d : ℝ} (hcd : c < d) {v : S} (hgd : g d = v) {B : Set S}
    (himage : ∀ t ∈ Ioo c d, g t ∈ f '' Icc a b ∩ B) :
    ∃ s ∈ Icc a b, f s = v ∧ s ∈ closure (Icc a b ∩ f ⁻¹' B) := by
  apply exists_period_parameter_in_closure_preimage hf
  have hd : d ∈ closure (Ioo c d) := by
    rw [closure_Ioo hcd.ne]
    exact ⟨hcd.le, le_rfl⟩
  rw [← hgd]
  have hsub : g '' Ioo c d ⊆ f '' Icc a b ∩ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact himage t ht
  exact closure_mono hsub (image_closure_subset_closure_image hg ⟨d, hd, rfl⟩)

/-- When local sides lie in disjoint labelled corner sets, an
accumulating corner must be one of those two labels. -/
theorem side_label_of_closure_preimage
    {S ι : Type*} {f : ℝ → S} {C : Set ℝ} {Q : ι → Set S}
    (hdis : Pairwise (fun i j => Disjoint (Q i) (Q j))) {i j k : ι}
    {s ε : ℝ} (hε : 0 < ε) (hfs : f s ∉ Q k)
    (hs : s ∈ closure (C ∩ f ⁻¹' Q k))
    (hL : ∀ t ∈ C, t ∈ Ioo (s - ε) s → f t ∈ Q i)
    (hR : ∀ t ∈ C, t ∈ Ioo s (s + ε) → f t ∈ Q j) : k = i ∨ k = j := by
  rcases exists_side_meeting_of_closure_preimage hε hfs hs hL hR with hleft | hright
  · left
    by_contra hki
    obtain ⟨z, hzk, hzi⟩ := hleft
    exact disjoint_left.mp (hdis hki) hzk hzi
  · right
    by_contra hkj
    obtain ⟨z, hzk, hzj⟩ := hright
    exact disjoint_left.mp (hdis hkj) hzk hzj

end GraphMinor.GM12
