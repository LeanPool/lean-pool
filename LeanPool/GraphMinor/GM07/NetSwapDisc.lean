/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# A model for pasting two closed discs along boundary arcs

In the net exchange of VII (2.6), page 218, cutting along the
proper line gives two discs. Pasting the selected side to its
mate joins those discs along a boundary arc. Map each disc to
one half of the unit disc, sending the pasted arc to the same
diameter. This gives an explicit disc model, with exactly the
prescribed identifications between the two pieces.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

universe u v

variable {S : Type u} [TopologicalSpace S]

/-- The disc model for the pasting step in VII (2.6), page 218.
The images of the pieces cover the closed unit disc, and a
point of one piece equals a point of the other precisely at
the paired boundary parameters. -/
theorem exists_disc_pasting_model
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : 𝕀 → X) (g : 𝕀 → Y) (hf : IsArcMap f) (hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B) :
    ∃ (p : X → ℂ) (q : Y → ℂ),
      ContinuousOn p A ∧ ContinuousOn q B ∧ InjOn p A ∧ InjOn q B ∧
      p '' A ∪ q '' B = closedBall 0 1 ∧
      (∀ x ∈ A, ∀ y ∈ B, p x = q y ↔ ∃ t, x = f t ∧ y = g t) ∧
      ∀ t, p (f t) = q (g t) := by
  obtain ⟨a, b, cut⟩ := exists_cut_diameter
  obtain ⟨p, p', hpc, hp'c, hpm, hp'm, hpi, hp'i, hpf, hpbd⟩ :=
    exists_pasting_half_coordinates hA hf.1 hf.2 hfbd cut.arc_a cut.arc_e
      cut.a_zero cut.a_one cut.a_eq_e
  obtain ⟨q, q', hqc, hq'c, hqm, hq'm, hqi, hq'i, hqg, hqbd⟩ :=
    exists_pasting_half_coordinates hB hg.1 hg.2 hgbd cut.arc_b cut.arc_e
      cut.b_zero cut.b_one cut.symm.a_eq_e
  obtain ⟨φ⟩ := oArc_sphere
  obtain ⟨hunion, -, -, hmeet, -, -⟩ := cut.closedInner_facts (isJordanParts φ)
  rw [closedInner_sphere] at hunion
  have hpimage : p '' A = closedInner (side a unitDiscDiameter) :=
    Subset.antisymm hpm.image_subset (fun z hz => ⟨p' z, hp'm hz, hp'i hz⟩)
  have hqimage : q '' B = closedInner (side b unitDiscDiameter) :=
    Subset.antisymm hqm.image_subset (fun z hz => ⟨q' z, hq'm hz, hq'i hz⟩)
  have hfA : ∀ t, f t ∈ A := fun t => discBd_subset A (hfbd ⟨t, rfl⟩)
  have hgB : ∀ t, g t ∈ B := fun t => discBd_subset B (hgbd ⟨t, rfl⟩)
  refine ⟨p, q, hpc, hqc, hpi.injOn, hqi.injOn, ?_, ?_, ?_⟩
  · rw [hpimage, hqimage]
    exact hunion
  · intro x hx y hy
    constructor
    · intro hxy
      have hm : p x ∈ closedInner (side a unitDiscDiameter) ∩
          closedInner (side b unitDiscDiameter) :=
        ⟨hpm hx, hxy.symm ▸ hqm hy⟩
      obtain ⟨t, ht⟩ := hmeet hm
      refine ⟨t, hpi.injOn hx (hfA t) ?_, hqi.injOn hy (hgB t) ?_⟩
      · exact ht.symm.trans (hpf t).symm
      · exact hxy.symm.trans (ht.symm.trans (hqg t).symm)
    · rintro ⟨t, rfl, rfl⟩
      exact (hpf t).trans (hqg t).symm
  · intro t
    exact (hpf t).trans (hqg t).symm

end GraphMinor.GM07
