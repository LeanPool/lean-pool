/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossingPoints
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Carrying the source crossings through an embedding

In XII (4.5), page 252, the plane drawing is carried into the
surface. An injective map preserves every edge meeting and
creates none, including the exclusion of vertex points. Thus
the one-crossing equations transport exactly. A continuous
injective map also carries each simple edge arc to a simple
edge arc with the corresponding ends.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- An injective map preserves exactly the edge meetings away
from vertices. This carries the source crossing set into the
surface in XII (4.5), page 252. -/
theorem edgeMeetingPoints_image {X Y V E : Type*} (f : X → Y) (hf : Function.Injective f)
    (v : V → X) (P : E → Set X) :
    edgeMeetingPoints (f ∘ v) (fun e => f '' P e) = f '' edgeMeetingPoints v P := by
  ext z
  constructor
  · rintro ⟨i, j, hij, ⟨hzi, hzj⟩, hzV⟩
    obtain ⟨x, hxi, hxz⟩ := hzi
    obtain ⟨y, hyj, hyz⟩ := hzj
    have hyx : y = x := hf (hyz.trans hxz.symm)
    have hxj : x ∈ P j := hyx ▸ hyj
    refine ⟨x, ⟨i, j, hij, ⟨hxi, hxj⟩, ?_⟩, hxz⟩
    rintro ⟨w, hw⟩
    exact hzV ⟨w, (congrArg f hw).trans hxz⟩
  · rintro ⟨x, ⟨i, j, hij, hx, hxV⟩, rfl⟩
    refine ⟨i, j, hij, ⟨mem_image_of_mem _ hx.1, mem_image_of_mem _ hx.2⟩, ?_⟩
    rintro ⟨w, hw⟩
    exact hxV ⟨w, hf hw⟩

/-- The single-meeting equation of an edge is unchanged by an
injective map, with its selected meeting point carried along. -/
theorem one_meeting_image {X Y V E : Type*} (f : X → Y) (hf : Function.Injective f)
    (v : V → X) (P : E → Set X) {e : E} {x : X}
    (h : P e ∩ edgeMeetingPoints v P = {x}) :
    f '' P e ∩ edgeMeetingPoints (f ∘ v) (fun j => f '' P j) = {f x} := by
  rw [edgeMeetingPoints_image f hf, ← image_inter hf, h, image_singleton]

/-- A continuous injective map carries a simple arc to a simple
arc with the image endpoints. -/
theorem isLineWithEnds_image_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (hinj : Function.Injective f) {L : Set X} {a b : X} (hL : IsLineWithEnds L a b) :
    IsLineWithEnds (f '' L) (f a) (f b) := by
  obtain ⟨g, hg, hgr, hg0, hg1⟩ := hL.exists_arc
  have hfg : IsArcMap (f ∘ g) := ⟨hf.comp hg.1, hinj.comp hg.2⟩
  have h := hfg.isLineWithEnds
  simpa only [range_comp, hgr, Function.comp_apply, hg0, hg1] using h

end GraphMinor.GM12
