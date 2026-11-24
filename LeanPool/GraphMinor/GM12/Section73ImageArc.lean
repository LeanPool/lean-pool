/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.ContinuousMap.Basic
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Edge lines under a contraction map

In XII (7.3), page 261, contracting one radial edge preserves the
other edge lines when the contraction is injective on each of their
closures. Parameterize a line, compose with the map, and use the
resulting embedded interval. Compactness also lets the image commute
with taking an edge closure.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A continuous map injective on a line preserves that line and its
specified ends, as needed for the edge contractions in XII (7.3). -/
theorem lineWithEnds_image_of_injOn
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T2Space T]
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) {f : S → T}
    (hf : ContinuousOn f L) (hinj : InjOn f L) :
    IsLineWithEnds (f '' L) (f u) (f v) := by
  obtain ⟨p, hp0, hp1⟩ := hL
  let q : unitInterval → T := fun t => f (p t).val
  have hqc : Continuous q := hf.comp_continuous
    (continuous_subtype_val.comp p.continuous) (fun t => (p t).property)
  have hqi : Function.Injective q := by
    intro s t hst
    exact p.injective (Subtype.ext (hinj (p s).property (p t).property hst))
  have hrange : range q = f '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(p t).val, (p t).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨p.symm ⟨z, hz⟩, congrArg f (congrArg Subtype.val (p.apply_symm_apply ⟨z, hz⟩))⟩
  simpa only [q, hp0, hp1, hrange] using isLine_range hqc hqi

/-- The two specified ends of a line are distinct. -/
theorem lineWithEnds_ends_ne {S : Type*} [TopologicalSpace S]
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) : u ≠ v := by
  obtain ⟨p, hp0, hp1⟩ := hL
  intro huv
  exact (zero_ne_one : (0 : unitInterval) ≠ 1)
    (p.injective (Subtype.ext (hp0.trans (huv.trans hp1.symm))))

/-- A continuous map commutes with closure on a set with compact
closure. This identifies the closures of the surviving edge images. -/
theorem closure_image_eq_of_compact_closure
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T2Space T]
    {f : S → T} (hf : Continuous f) {A : Set S} (hA : IsCompact (closure A)) :
    closure (f '' A) = f '' closure A := by
  exact Subset.antisymm
    (closure_minimal (image_mono subset_closure) (hA.image hf).isClosed)
    (image_closure_subset_closure_image hf)

end GraphMinor.GM12
