/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EmbeddedContactDiscs
public import LeanPool.GraphMinor.GM12.Section4CrossingContactLocation
public import LeanPool.GraphMinor.GM12.Section4CrossDiscQuadrants
public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.Surface.Wedge
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Opposite endpoint classes after embedding the source

For XII (4.5), claim (1), page 253, carry the crossing discs
and one-crossing arcs into a surface chart and form the vertex
contact discs. Each residual edge end lies on its own crossing
disc. The two ends are distinct, so their unordered pair is
exactly the corresponding opposite pair of quarter-turn marks.
This identifies the geometric contact classes with the edge
ends used later to index the external paths.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- The embedded source has disjoint vertex contact discs whose
edge-end pairs are exactly the two marked opposite pairs at
each crossing. This assembles the endpoint classes in
XII (4.5), claim (1), page 253. -/
theorem exists_embedded_opposite_contacts {S V E : Type}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite V] [Finite E]
    (hS : IsClosedSurface S) (f : ℂ → S) (hf : Topology.IsOpenEmbedding f)
    (v : V → ℂ) (hinj : Function.Injective v) (κ : E × Bool → V) (P : E → Set ℂ)
    (hP : ∀ e, IsLineWithEnds (P e) (v (κ (e, false))) (v (κ (e, true))))
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x})
    (hM : (edgeMeetingPoints v P).Finite)
    (σ : (edgeMeetingPoints v P × Bool) ≃ E)
    (A : edgeMeetingPoints v P → ℂ ≃L[ℝ] ℂ)
    (r : edgeMeetingPoints v P → ℝ) (D : edgeMeetingPoints v P → Set ℂ)
    (hpair : ∀ x, x.val ∈ P (σ (x, false)) ∩ P (σ (x, true)))
    (hD : ∀ x, IsClosedDisc (D x))
    (hcentre : ∀ x, x.val ∈ interior (D x)) (hDv : ∀ x, Disjoint (D x) (range v))
    (hDP : ∀ x e, e ≠ σ (x, false) → e ≠ σ (x, true) → Disjoint (D x) (P e))
    (hleft : ∀ x, P (σ (x, false)) ∩ discBd (D x) =
      {x.val + A x (r x • (1 : ℂ)), x.val + A x ((-r x) • (1 : ℂ))})
    (hright : ∀ x, P (σ (x, true)) ∩ discBd (D x) =
      {x.val + A x (r x • Complex.I), x.val + A x ((-r x) • Complex.I)}) :
    ∃ (q : E × Bool → S) (B : V → Set S), Function.Injective q ∧
      (∀ w, IsClosedDisc (B w)) ∧ (∀ w z, w ≠ z → Disjoint (B w) (B z)) ∧
      (∀ w, B w ∩ (⋃ x, f '' D x) = edgeEndClass q κ w) ∧
      (∀ x, ({q (σ (x, false), false), q (σ (x, false), true)} : Set S) =
        {f (crossDiscParam (A x) x.val (r x) (ee 0)),
          f (crossDiscParam (A x) x.val (r x) (ee (1 / 2)))}) ∧
      (∀ x, ({q (σ (x, true), false), q (σ (x, true), true)} : Set S) =
        {f (crossDiscParam (A x) x.val (r x) (ee (1 / 4))),
          f (crossDiscParam (A x) x.val (r x) (ee (3 / 4)))}) := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  classical
  let X := edgeMeetingPoints v P
  let : Fintype X := hM.fintype
  let Z := ⋃ x : X, D x
  have hZ : IsCompact Z := isCompact_iUnion (fun x => (hD x).isCompact)
  have hvZ : ∀ w, v w ∉ Z := by
    intro w hw
    obtain ⟨x, hx⟩ := mem_iUnion.mp hw
    exact disjoint_left.mp (hDv x) hx (mem_range_self w)
  have hMZ : X ⊆ interior Z := by
    intro z hz
    exact interior_mono (subset_iUnion D ⟨z, hz⟩) (hcentre ⟨z, hz⟩)
  obtain ⟨q, B, hq, hqGeom, hB, hBB, hBcontact⟩ := exists_embedded_contact_discs
    hS f hf v hinj κ P hP hPV hcross Z hZ hvZ hMZ
  have hZi : f '' Z = ⋃ x : X, f '' D x := image_iUnion
  have himage : ∀ x : X, IsClosedDisc (f '' D x) ∧ discBd (f '' D x) = f '' discBd (D x) :=
    fun x => Surface.isClosedDisc_image_injOn (hD x) (hD x).isCompact hf.continuous.continuousOn
      hf.injective.injOn
  have hxrange : range (Subtype.val : X → ℂ) = X := by
    ext z
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  have hmeet : ∀ x : X, ∀ b : Bool, P (σ (x, b)) ∩ X = {x.val} := by
    intro x b
    obtain ⟨z, hz, hmeet⟩ := hcross (σ (x, b))
    have hxP : x.val ∈ P (σ (x, b)) := by
      cases b
      · exact (hpair x).1
      · exact (hpair x).2
    have hxz : x.val = z := mem_singleton_iff.mp (hmeet.subset ⟨hxP, x.property⟩)
    rwa [← hxz] at hmeet
  have hmeetImage : ∀ x : X, ∀ b : Bool,
      (f '' P (σ (x, b))) ∩ range (fun y : X => f y.val) = {f x.val} := by
    intro x b
    change (f '' P (σ (x, b))) ∩ range (f ∘ (Subtype.val : X → ℂ)) = _
    rw [range_comp, hxrange, ← image_inter hf.injective, hmeet, image_singleton]
  have hpairImage : ∀ x : X, f x.val ∈ (f '' P (σ (x, false))) ∩ (f '' P (σ (x, true))) :=
    fun x => ⟨mem_image_of_mem f (hpair x).1, mem_image_of_mem f (hpair x).2⟩
  have havoidImage : ∀ x : X, ∀ e, e ≠ σ (x, false) → e ≠ σ (x, true) →
      Disjoint (f '' D x) (f '' P e) := fun x e hl hr =>
    (disjoint_image_iff hf.injective).mpr (hDP x e hl hr)
  have hqgeom : ∀ i, q i ∈ (f '' P i.1) ∩ frontier (⋃ x : X, f '' D x) := by
    intro i
    rw [← hZi]
    exact hqGeom i
  refine ⟨q, B, hq, hB, hBB, ?_, ?_, ?_⟩
  · intro w
    rw [← hZi]
    exact hBcontact w
  · intro x
    obtain ⟨h0, -, h2, -⟩ := crossDiscParam_quarter_values (A x) x.val (r x)
    have hbd : (f '' P (σ (x, false))) ∩ discBd (f '' D x) =
        {f (crossDiscParam (A x) x.val (r x) (ee 0)), f (crossDiscParam (A x) x.val (r x) (ee
          (1 / 2)))} := by
      rw [(himage x).2, ← image_inter hf.injective, hleft, image_pair, h0, h2]
    exact crossing_contact_pair_eq hS (fun x : X => f '' D x) (fun x => (himage x).1)
      (fun x : X => f x.val) (hf.injective.comp Subtype.val_injective)
      (fun e => f '' P e) (fun x => σ (x, false)) (fun x => σ (x, true)) hpairImage havoidImage
      (σ (x, false)) x (hmeetImage x false) hbd
      (fun h => Bool.false_ne_true (congrArg Prod.snd (hq h))) (hqgeom (σ (x, false), false))
        (hqgeom (σ (x, false), true))
  · intro x
    obtain ⟨-, h1, -, h3⟩ := crossDiscParam_quarter_values (A x) x.val (r x)
    have hbd : (f '' P (σ (x, true))) ∩ discBd (f '' D x) =
        {f (crossDiscParam (A x) x.val (r x) (ee (1 / 4))), f (crossDiscParam (A x) x.val (r x) (ee
          (3 / 4)))} := by
      rw [(himage x).2, ← image_inter hf.injective, hright, image_pair, h1, h3]
    exact crossing_contact_pair_eq hS (fun x : X => f '' D x) (fun x => (himage x).1)
      (fun x : X => f x.val) (hf.injective.comp Subtype.val_injective)
      (fun e => f '' P e) (fun x => σ (x, false)) (fun x => σ (x, true)) hpairImage havoidImage
      (σ (x, true)) x (hmeetImage x true) hbd
      (fun h => Bool.false_ne_true (congrArg Prod.snd (hq h))) (hqgeom (σ (x, true), false))
        (hqgeom (σ (x, true), true))

end GraphMinor.GM12
