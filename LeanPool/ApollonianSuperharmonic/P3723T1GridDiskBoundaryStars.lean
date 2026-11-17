/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3723T1GridDiskPairedModel
public import LeanPool.ApollonianSuperharmonic.P3723T1ConvexRadialIntersection
public import LeanPool.ApollonianSuperharmonic.P3723T1ConvexRadialParameterization
public import LeanPool.ApollonianSuperharmonic.P3723T1PairedModelSegmentPullback

/-!
# P3723T1GridDiskBoundaryStars

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

-- [TABLET NODE: P3723T1GridDiskBoundaryStars]
theorem P3723T1GridDiskBoundaryStars {ι : Type}
    (T : ProtoTile) (hT : LatticeTile T)
    (x : Real × Real) (hx : x ∈ interior (TileRealization T))
    (port : ι → Real × Real)
    (hport : ∀ i, port i ∈ frontier (TileRealization T))
    (hinj : Function.Injective port) :
    ∃ g : ι → Icc (0 : Real) 1 → Real × Real,
      (∀ i, Continuous (g i) ∧ Function.Injective (g i) ∧
        g i ⟨0, by norm_num⟩ = x ∧
        g i ⟨1, by norm_num⟩ = port i ∧
        Nonempty (P3723T1PolygonalParameterization (g i))) ∧
      (∀ i, Set.range (g i) ⊆ interior (TileRealization T) ∪ {port i}) ∧
      ∀ i j, i ≠ j → Set.range (g i) ∩ Set.range (g j) = {x} := by
-- BODY
  classical
  obtain ⟨n, p, v, K, t, h, _hvertex, _hedges, _hfrontier, hboundary,
    _hinterior, haffine⟩ := P3723T1GridDiskPairedModel T hT
  let X := TileRealization T
  have hX : IsClosed X :=
    (P3381T1TriangulationBoundary p X K t).1.isClosed
  have hK : IsClosed K := t.target_closed
  have hconv : Convex Real K := t.target_convex
  let xX : X := ⟨x, interior_subset hx⟩
  let pX : ι → X := fun i => ⟨port i, hX.frontier_subset (hport i)⟩
  have hint : ∀ q : X,
      (q : Real × Real) ∈ interior X ↔ (h q : Real × Real) ∈ interior K := by
    intro q
    rw [mem_interior_iff_notMem_frontier q.property,
      mem_interior_iff_notMem_frontier (h q).property]
    exact not_congr (hboundary q)
  have hxK : (h xX : Real × Real) ∈ interior K := (hint xX).mp hx
  have hpK : ∀ i, (h (pX i) : Real × Real) ∈ frontier K :=
    fun i => (hboundary (pX i)).mp (hport i)
  have hpKinj : Function.Injective (fun i => (h (pX i) : Real × Real)) := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val (h.injective (Subtype.ext hij))
  obtain ⟨r, hr0, hr1, hrsub, hrline⟩ :
      ∃ r : ∀ i, Icc (0 : Real) 1 ≃ₜ
        segment Real (h xX : Real × Real) (h (pX i) : Real × Real),
        (∀ i, ((r i ⟨0, by norm_num⟩ :
          segment Real (h xX : Real × Real) (h (pX i) : Real × Real)) :
            Real × Real) = (h xX : Real × Real)) ∧
        (∀ i, ((r i ⟨1, by norm_num⟩ :
          segment Real (h xX : Real × Real) (h (pX i) : Real × Real)) :
            Real × Real) = (h (pX i) : Real × Real)) ∧
        (∀ i, segment Real (h xX : Real × Real) (h (pX i) : Real × Real) ⊆
          interior K ∪ {(h (pX i) : Real × Real)}) ∧
        (∀ i s, ((r i s : segment Real (h xX : Real × Real)
          (h (pX i) : Real × Real)) : Real × Real) =
            (1 - (s : Real)) • (h xX : Real × Real) +
              (s : Real) • (h (pX i) : Real × Real)) := by
    choose r hr0 hr1 hrsub hrline using fun i =>
      P3723T1ConvexRadialParameterization K hconv hK (h xX) (h (pX i)) hxK (hpK i)
    exact ⟨r, hr0, hr1, hrsub, hrline⟩
  let R : ι → Icc (0 : Real) 1 → K := fun i t =>
    ⟨r i t, hconv.segment_subset (h xX).property (h (pX i)).property
      (r i t).property⟩
  let g : ι → Icc (0 : Real) 1 → Real × Real := fun i t => h.symm (R i t)
  have hgcont : ∀ i, Continuous (g i) := by
    intro i
    have hRcont : Continuous (R i) :=
      Continuous.subtype_mk (continuous_subtype_val.comp (r i).continuous) _
    exact continuous_subtype_val.comp (h.symm.continuous.comp hRcont)
  have hginj : ∀ i, Function.Injective (g i) := by
    intro i s t hst
    apply (r i).injective
    apply Subtype.ext
    have hRt : R i s = R i t := h.symm.injective (Subtype.ext hst)
    exact congrArg (fun a : K => (a : Real × Real)) hRt
  have hg0 : ∀ i, g i ⟨0, by norm_num⟩ = x := by
    intro i
    have hR0 : R i ⟨0, by norm_num⟩ = h xX := Subtype.ext (hr0 i)
    change (h.symm (R i ⟨0, by norm_num⟩) : Real × Real) = x
    rw [hR0, h.symm_apply_apply]
  have hg1 : ∀ i, g i ⟨1, by norm_num⟩ = port i := by
    intro i
    have hR1 : R i ⟨1, by norm_num⟩ = h (pX i) := Subtype.ext (hr1 i)
    change (h.symm (R i ⟨1, by norm_num⟩) : Real × Real) = port i
    rw [hR1, h.symm_apply_apply]
  have hgpoly : ∀ i, Nonempty (P3723T1PolygonalParameterization (g i)) := by
    intro i
    let gi : Icc (0 : Real) 1 → X := fun s => h.symm (R i s)
    have hgi : ∀ s, (h (gi s) : Real × Real) =
        (1 - (s : Real)) • (h xX : Real × Real) +
          (s : Real) • (h (pX i) : Real × Real) := by
      intro s
      change (h (h.symm (R i s)) : Real × Real) = _
      rw [h.apply_symm_apply]
      exact hrline i s
    exact P3723T1PairedModelSegmentPullback p X K t h haffine
      (h xX) (h (pX i)) gi hgi
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hgcont i, hginj i, hg0 i, hg1 i, hgpoly i⟩
  · intro i q hq
    obtain ⟨t, rfl⟩ := hq
    rcases hrsub i (r i t).property with hi | hp
    · apply Or.inl
      apply (hint (h.symm (R i t))).mpr
      simpa only [h.apply_symm_apply] using hi
    · apply Or.inr
      have hRp : R i t = h (pX i) := Subtype.ext hp
      change (h.symm (R i t) : Real × Real) = port i
      rw [hRp, h.symm_apply_apply]
  · intro i j hij
    ext q
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
      have hR : R i t = R j s :=
        h.symm.injective (Subtype.ext hs.symm)
      have hm : (R i t : Real × Real) ∈
          segment Real (h xX : Real × Real) (h (pX i) : Real × Real) ∩
            segment Real (h xX : Real × Real) (h (pX j) : Real × Real) := by
        refine ⟨(r i t).property, ?_⟩
        rw [hR]
        exact (r j s).property
      rw [P3723T1ConvexRadialIntersection K hconv hK
        (h xX) (h (pX i)) (h (pX j)) hxK (hpK i) (hpK j)
          (hpKinj.ne hij)] at hm
      have hRx : R i t = h xX := Subtype.ext hm
      change (h.symm (R i t) : Real × Real) = x
      rw [hRx, h.symm_apply_apply]
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      rw [hq]
      exact ⟨⟨⟨0, by norm_num⟩, hg0 i⟩, ⟨⟨0, by norm_num⟩, hg0 j⟩⟩

end ApollonianSuperharmonic

end
