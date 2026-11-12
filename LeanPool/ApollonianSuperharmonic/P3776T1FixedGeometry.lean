/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3776T1OpenStar
public import LeanPool.ApollonianSuperharmonic.P3767T1FixedFaceComponents
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring

-- [TABLET NODE: P3776T1FixedGeometry]

/-!
# P3776T1FixedGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FixedPeriodicGeometryProof

private theorem hfree :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : P.lattice), ∀ (v : P.lattice), ∀ (a : ι),
        (P.shift u a = P.shift v a) → (u = v) := by
  classical
  intro ι P u v a h
  have hpos := congrArg P.plane.position h
  rw [P.position_periodic u a, P.position_periodic v a] at hpos
  have hvec : GaussianRealPoint (u : GaussianInt) =
      GaussianRealPoint (v : GaussianInt) := add_left_cancel hpos
  simp only [GaussianRealPoint, Prod.mk.injEq] at hvec
  apply Subtype.ext
  apply Zsqrtd.ext
  · exact_mod_cast hvec.1
  · exact_mod_cast hvec.2

private theorem hnonzero :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∃ u : P.lattice, u ≠ 0 := by
  classical
  intro ι P
  by_contra h
  have hz : ∀ u : P.lattice, u = 0 := by simpa using h
  have hrep : ∀ x : GaussianInt, x ∈ P.latticeReps := by
    intro x
    obtain ⟨r, ⟨hr, hxr⟩, _⟩ := P.lattice_full_rank x
    have heq : x - r = 0 := congrArg Subtype.val (hz ⟨x - r, hxr⟩)
    simpa [sub_eq_zero.mp heq] using hr
  have hinj : Function.Injective (fun n : ℕ => (n : GaussianInt)) :=
    Nat.cast_injective
  have hfinite := P.latticeReps.finite_toSet.preimage hinj.injOn
  have hall : (fun n : ℕ => (n : GaussianInt)) ⁻¹'
      (P.latticeReps : Set GaussianInt) = Set.univ := by
    ext n
    simp [hrep]
  rw [hall] at hfinite
  exact Set.infinite_univ hfinite

private theorem hinhab :
    ∀ (ι : Type), (PeriodicTileCore ι) → (Nonempty ι) := by
  classical
  intro ι P
  have hcover : (0 : Real × Real) ∈
      Set.range P.plane.position ∪
        {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ P.plane.edgeArc a b} ∪
        {p | ∃ f, p ∈ P.plane.faceRegion f} := by
    rw [P.plane.plane_cover]
    trivial
  rcases hcover with (⟨a, _⟩ | ⟨a, b, _⟩) | ⟨f, _⟩
  · exact ⟨a⟩
  · exact ⟨a⟩
  · exact ⟨P.plane.faceVertex f 0⟩

private theorem harc :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
        (IsCompact (P.plane.edgeArc a b)) := by
  classical
  intro ι P a b hab
  obtain ⟨h, _, _⟩ := P.plane.arc_homeomorph a b hab
  have : CompactSpace (Set.Icc (0 : Real) 1) := inferInstance
  have hs : Set.range (fun t : Set.Icc (0 : Real) 1 =>
      ((h t : P.plane.edgeArc a b) : Real × Real)) = P.plane.edgeArc a b := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (h t).property
    · intro hx
      exact ⟨h.symm ⟨x, hx⟩, by simp⟩
  rw [← hs]
  exact isCompact_range (continuous_subtype_val.comp h.continuous)

private theorem hexterior :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∃ u : P.lattice, u ≠ 0) → (∀ (B : Real),
        IsPreconnected {x : Real × Real | B < ‖x‖}) := by
  classical
  intro ι P hnonzero B
  let R : Set (Real × Real) := Set.Ioi B ×ˢ Set.univ
  let T : Set (Real × Real) := Set.univ ×ˢ Set.Ioi B
  let L : Set (Real × Real) := Set.Iio (-B) ×ˢ Set.univ
  let D : Set (Real × Real) := Set.univ ×ˢ Set.Iio (-B)
  have hR : IsPreconnected R := isPreconnected_Ioi.prod isPreconnected_univ
  have hT : IsPreconnected T := isPreconnected_univ.prod isPreconnected_Ioi
  have hL : IsPreconnected L := isPreconnected_Iio.prod isPreconnected_univ
  have hD : IsPreconnected D := isPreconnected_univ.prod isPreconnected_Iio
  have hRT : IsPreconnected (R ∪ T) :=
    hR.union' ⟨(B + 1, B + 1), by simp [R, T]⟩ hT
  have hRTL : IsPreconnected (R ∪ T ∪ L) :=
    hRT.union' ⟨(-B - 1, B + 1), by simp [R, T, L]⟩ hL
  have hRTLD : IsPreconnected (R ∪ T ∪ L ∪ D) :=
    hRTL.union' ⟨(-B - 1, -B - 1), by simp [R, T, L, D]⟩ hD
  have heq : {x : Real × Real | B < ‖x‖} = R ∪ T ∪ L ∪ D := by
    ext x
    simp only [Set.mem_ofPred_eq, Prod.norm_def, Real.norm_eq_abs, lt_max_iff,
      lt_abs, Set.mem_union, R, T, L, D, Set.mem_prod, Set.mem_Ioi,
      Set.mem_Iio, Set.mem_univ, and_true, true_and]
    have h1 : B < -x.1 ↔ x.1 < -B := by constructor <;> intro h <;> linarith
    have h2 : B < -x.2 ↔ x.2 < -B := by constructor <;> intro h <;> linarith
    rw [h1, h2]
    tauto
  rw [heq]
  exact hRTLD

private theorem hcompact :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∃ u : P.lattice, u ≠ 0) → ((∀ (u : P.lattice), ∀
        (f : P.plane.Face), (P.faceShift u f = f) → (u = 0)) → ((∀ (f : P.plane.Face), IsCompact
        (frontier (P.plane.faceRegion f))) → ((∀ (B : Real), IsPreconnected {x : Real × Real | B
        < ‖x‖}) → (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f)))))) := by
  classical
  intro ι P hnonzero hfacefree hfront hexterior f
  apply Bornology.IsBounded.isCompact_closure
  by_contra hunbounded
  obtain ⟨B, hB, hbound⟩ := (hfront f).isBounded.exists_pos_norm_le
  have hmeet : ({x : Real × Real | B < ‖x‖} ∩ P.plane.faceRegion f).Nonempty := by
    by_contra h
    apply hunbounded
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B, fun x hx => ?_⟩
    by_contra hle
    exact h ⟨x, lt_of_not_ge hle, hx⟩
  have houtside : {x : Real × Real | B < ‖x‖} ⊆ P.plane.faceRegion f :=
    P3767T1BarrierRegionMaximal _ _ _ (P.plane.region_open f)
      (Set.Subset.refl _) (hexterior B)
      (Set.disjoint_left.mpr (fun x hx hxf => (not_lt_of_ge (hbound x hxf)) hx)) hmeet
  obtain ⟨u, hu⟩ := hnonzero
  let y : Real × Real := (B + |(GaussianRealPoint u).1| + 1, 0)
  have hy : B < ‖y‖ := by
    have hh : B < ‖y.1‖ := by
      change B < |B + |(GaussianRealPoint u).1| + 1|
      linarith [le_abs_self (B + |(GaussianRealPoint u).1| + 1),
        abs_nonneg (GaussianRealPoint u).1]
    exact hh.trans_le (norm_fst_le y)
  have hyu : B < ‖y - GaussianRealPoint u‖ := by
    have hfst := norm_fst_le (y - GaussianRealPoint u)
    change ‖B + |(GaussianRealPoint u).1| + 1 - (GaussianRealPoint u).1‖ ≤
      ‖y - GaussianRealPoint u‖ at hfst
    rw [Real.norm_eq_abs] at hfst
    have hh := le_abs_self (B + |(GaussianRealPoint u).1| + 1 - (GaussianRealPoint u).1)
    linarith [le_abs_self (GaussianRealPoint u).1]
  have hys : y ∈ P.plane.faceRegion (P.faceShift u f) := by
    rw [P.faceRegion_periodic]
    exact ⟨y - GaussianRealPoint u, houtside hyu, sub_add_cancel _ _⟩
  exact Set.disjoint_left.mp
    (P.plane.region_disjoint (fun h => hu (hfacefree u f h.symm))) (houtside hy) hys

private theorem hfiniteTrans :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (K : Set (Real × Real)), ∀ (A : Set (Real ×
        Real)), (IsCompact K) → ((IsCompact A) → (Set.Finite {u : P.lattice |
        (K ∩ (fun x => x + GaussianRealPoint u) '' A).Nonempty})) := by
  classical
  intro ι P K A hK hA
  obtain ⟨C, _, hC⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨D, _, hD⟩ := hA.isBounded.exists_pos_norm_le
  let N : ℤ := Int.ceil (C + D)
  have hN : C + D ≤ (N : Real) := Int.le_ceil _
  have hinj : Function.Injective (fun u : P.lattice =>
      ((u : GaussianInt).re, (u : GaussianInt).im)) := by
    intro u v h
    apply Subtype.ext
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  apply (((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).preimage hinj.injOn).subset
  rintro u ⟨x, hx, y, hy, hxy⟩
  have hv : GaussianRealPoint u = x - y := by
    have hh : y + GaussianRealPoint u = x := hxy
    rw [← hh]
    exact (add_sub_cancel_left y (GaussianRealPoint u)).symm
  have hb : ‖GaussianRealPoint u‖ ≤ C + D := by
    rw [hv]
    exact (norm_sub_le x y).trans (add_le_add (hC x hx) (hD y hy))
  have hre : |((u : GaussianInt).re : Real)| ≤ (N : Real) :=
    (norm_fst_le (GaussianRealPoint u)).trans (hb.trans hN)
  have him : |((u : GaussianInt).im : Real)| ≤ (N : Real) :=
    (norm_snd_le (GaussianRealPoint u)).trans (hb.trans hN)
  change (-N ≤ (u : GaussianInt).re ∧ (u : GaussianInt).re ≤ N) ∧
    (-N ≤ (u : GaussianInt).im ∧ (u : GaussianInt).im ≤ N)
  constructor
  · constructor
    · exact_mod_cast (abs_le.mp hre).1
    · exact_mod_cast (abs_le.mp hre).2
  · constructor
    · exact_mod_cast (abs_le.mp him).1
    · exact_mod_cast (abs_le.mp him).2

private theorem hfiniteFace :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∀ (f : P.plane.Face), IsCompact (closure
        (P.plane.faceRegion f))) → ((∀ (K : Set (Real × Real)), ∀ (A : Set (Real × Real)),
        (IsCompact K) → ((IsCompact A) → (Set.Finite {u : P.lattice | (K ∩ (fun x => x +
        GaussianRealPoint u) '' A).Nonempty}))) → ((∀ (u : P.lattice), ∀ (f : P.plane.Face),
        closure (P.plane.faceRegion (P.faceShift u f)) = (fun x => x + GaussianRealPoint u) ''
        closure (P.plane.faceRegion f)) → (∀ (K : Set (Real × Real)), (IsCompact K) → (Set.Finite
        {f | (K ∩ closure (P.plane.faceRegion f)).Nonempty})))) := by
  classical
  intro ι P hcompact hfiniteTrans hclosurePeriodic K hK
  have hrep : Set.Finite (⋃ r ∈ P.faceOrbitReps,
      (fun u => P.faceShift u r) '' {u : P.lattice |
        (K ∩ (fun x => x + GaussianRealPoint u) ''
          closure (P.plane.faceRegion r)).Nonempty}) :=
    P.faceOrbitReps.finite_toSet.biUnion fun r _ =>
      (hfiniteTrans K _ hK (hcompact r)).image (fun u => P.faceShift u r)
  apply hrep.subset
  intro f hf
  obtain ⟨r, hr, u, rfl⟩ := P.face_orbit_representatives f
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
  refine ⟨u, ?_, rfl⟩
  change (K ∩ closure (P.plane.faceRegion (P.faceShift u r))).Nonempty at hf
  rwa [hclosurePeriodic] at hf

private theorem hboundaryEdge :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (f : P.plane.Face), ∀ (i : Fin 3), ∀ (j : Fin 3),
        (i ≠ j) → (P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆
        frontier (P.plane.faceRegion f)) := by
  classical
  intro ι P f i j hij
  rw [P.plane.face_boundary f]
  fin_cases i <;> fin_cases j <;> dsimp at *
  all_goals try exact (hij rfl).elim
  all_goals intro x hx
  all_goals first
    | exact Or.inl (Or.inl hx)
    | exact Or.inl (Or.inr hx)
    | exact Or.inr hx
    | rw [P.plane.arc_symmetric] at hx
      first
        | exact Or.inl (Or.inl hx)
        | exact Or.inl (Or.inr hx)
        | exact Or.inr hx

private theorem hedgeFace :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∀ (f : P.plane.Face), ∀ (i : Fin 3), ∀ (j : Fin
        3), (i ≠ j) → (P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆
        frontier (P.plane.faceRegion f))) → (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → (∃ f
        : P.plane.Face,
        (∃ i, P.plane.faceVertex f i = a) ∧
        (∃ j, P.plane.faceVertex f j = b) ∧
        P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f))) := by
  classical
  intro ι P hboundaryEdge a b hab
  obtain ⟨f, _, _, ⟨⟨i, hi⟩, ⟨j, hj⟩⟩, _, _⟩ :=
    P.plane.every_edge_two_faces a b hab
  have hij : i ≠ j := by
    intro h
    have heq : a = b := hi.symm.trans (h ▸ hj)
    exact P.plane.adjacent_irreflexive a (heq ▸ hab)
  refine ⟨f, ⟨i, hi⟩, ⟨j, hj⟩, ?_⟩
  rw [← hi, ← hj]
  exact (hboundaryEdge f i j hij).trans frontier_subset_closure

private theorem hcoverAt366 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ [Nontrivial ι], (∀ (a : ι), ∀ (b : ι),
        (P.plane.adjacent a b) → (∃ f : P.plane.Face, (∃ i, P.plane.faceVertex f i = a) ∧ (∃ j,
        P.plane.faceVertex f j = b) ∧ P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f))) →
        ((∀ (f : P.plane.Face), ∀ (i : Fin 3), P.plane.position (P.plane.faceVertex f i) ∈
        closure (P.plane.faceRegion f)) → (∀ (x : Real × Real), ∃ f, x ∈ closure
        (P.plane.faceRegion f))) := by
  classical
  intro ι P this hedgeFace hposFace x
  have hx : x ∈ Set.range P.plane.position ∪
      {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ P.plane.edgeArc a b} ∪
      {p | ∃ f, p ∈ P.plane.faceRegion f} := by
    rw [P.plane.plane_cover]
    trivial
  rcases hx with (⟨a, rfl⟩ | ⟨a, b, hab, hx⟩) | ⟨f, hx⟩
  · obtain ⟨b, hab⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
    obtain ⟨f, ⟨i, hi⟩, _, _⟩ := hedgeFace a b hab
    exact ⟨f, hi ▸ hposFace f i⟩
  · obtain ⟨f, _, _, hs⟩ := hedgeFace a b hab
    exact ⟨f, hs hx⟩
  · exact ⟨f, subset_closure hx⟩

private theorem harcMatch :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (d : ι),
        (P.plane.adjacent a b) → ((P.plane.adjacent c d) → (∀ (x : Real × Real), (x ∈
        P.plane.edgeArc a b) → ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → ((x ∈
        P.plane.edgeArc c d) → (({a, b} : Set ι) = {c, d})))))) := by
  classical
  intro ι P a b c d hab hcd x hx hxa hxb hy
  by_contra hne
  have hh : x ∈ P.plane.position '' (({a, b} : Set ι) ∩ {c, d}) := by
    rw [← P.plane.arc_intersections a b c d hab hcd hne]
    exact ⟨hx, hy⟩
  obtain ⟨v, hv, hvx⟩ := hh
  rcases Set.mem_insert_iff.mp hv.1 with rfl | hv
  · exact hxa hvx.symm
  · have hvb : v = b := Set.mem_singleton_iff.mp hv
    exact hxb (hvb ▸ hvx.symm)

private theorem hclosureVertex :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ [Nontrivial ι], (∀ (f : P.plane.Face),
        Disjoint (P3767T1FixedTrace P.plane) (P.plane.faceRegion f)) → (∀ (f : P.plane.Face), ∀
        (w : ι), (P.plane.position w ∈ closure (P.plane.faceRegion f)) → (∃ i, P.plane.faceVertex
        f i = w)) := by
  classical
  intro ι P this havoid f w hx
  rw [closure_eq_self_union_frontier] at hx
  rcases hx with hx | hx
  · exact (Set.disjoint_left.mp (havoid f) (Or.inl ⟨w, rfl⟩) hx).elim
  · rw [P.plane.face_boundary] at hx
    rcases hx with (hx | hx) | hx
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 0 1 (by decide)) hx with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 1 2 (by decide)) hx with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 2 0 (by decide)) hx with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨0, h.symm⟩

private theorem hclosureEdge :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∀ (f : P.plane.Face), Disjoint
        (P3767T1FixedTrace P.plane) (P.plane.faceRegion f)) → ((∀ (a : ι), ∀ (b : ι), ∀ (c :
        ι), ∀ (d : ι), (P.plane.adjacent a b) → ((P.plane.adjacent c d) → (∀ (x : Real × Real),
        (x ∈ P.plane.edgeArc a b) → ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → ((x ∈
        P.plane.edgeArc c d) → (({a, b} : Set ι) = {c, d}))))))) → (∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → (∀ (x : Real × Real), (x ∈ P.plane.edgeArc a b) →
        ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → ((x ∈ closure (P.plane.faceRegion
        f)) → ((∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b)))))))) := by
  classical
  intro ι P havoid harcMatch f a b hab x hx hxa hxb hxf
  have hpair (i j : Fin 3) (hij : i ≠ j)
      (hy : x ∈ P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j)) :
      (∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b) := by
    have heq := harcMatch a b _ _ hab (P.plane.face_edges f i j hij) x hx hxa hxb hy
    have ha : a ∈ ({P.plane.faceVertex f i, P.plane.faceVertex f j} : Set ι) :=
      heq ▸ (by simp)
    have hb : b ∈ ({P.plane.faceVertex f i, P.plane.faceVertex f j} : Set ι) :=
      heq ▸ (by simp)
    constructor
    · rcases Set.mem_insert_iff.mp ha with h | h
      · exact ⟨i, h.symm⟩
      · exact ⟨j, (Set.mem_singleton_iff.mp h).symm⟩
    · rcases Set.mem_insert_iff.mp hb with h | h
      · exact ⟨i, h.symm⟩
      · exact ⟨j, (Set.mem_singleton_iff.mp h).symm⟩
  rw [closure_eq_self_union_frontier] at hxf
  rcases hxf with hxf | hxf
  · exact (Set.disjoint_left.mp (havoid f) (Or.inr ⟨a, b, hab, hx⟩) hxf).elim
  · rw [P.plane.face_boundary] at hxf
    rcases hxf with (hy | hy) | hy
    · exact hpair 0 1 (by decide) hy
    · exact hpair 1 2 (by decide) hy
    · exact hpair 2 0 (by decide) hy

private theorem hstaropen :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ [Nontrivial ι], (∀ (a : ι), ∀ (b : ι),
        (P.plane.adjacent a b) → (IsCompact (P.plane.edgeArc a b))) → ((LocallyFinite (fun f =>
        closure (P.plane.faceRegion f))) → ((∀ (f : P.plane.Face), ∀ (i : Fin 3), ∀ (j : Fin 3),
        (i ≠ j) → (P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆ frontier
        (P.plane.faceRegion f))) → ((∀ (f : P.plane.Face), ∀ (i : Fin 3), P.plane.position
        (P.plane.faceVertex f i) ∈ closure (P.plane.faceRegion f)) → ((∀ (x : Real × Real), ∃ f,
        x ∈ closure (P.plane.faceRegion f)) → ((∀ (f : P.plane.Face), Disjoint
        (P3767T1FixedTrace P.plane) (P.plane.faceRegion f)) → ((∀ (a : ι), ∀ (b : ι), ∀ (c :
        ι), ∀ (d : ι), (P.plane.adjacent a b) → ((P.plane.adjacent c d) → (∀ (x : Real × Real),
        (x ∈ P.plane.edgeArc a b) → ((x ≠ P.plane.position a) → ((x ≠ P.plane.position b) → ((x ∈
        P.plane.edgeArc c d) → (({a, b} : Set ι) = {c, d}))))))) → ((∀ (f : P.plane.Face), ∀ (w :
        ι), (P.plane.position w ∈ closure (P.plane.faceRegion f)) → (∃ i, P.plane.faceVertex f i
        = w)) → ((∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → (∀ (x :
        Real × Real), (x ∈ P.plane.edgeArc a b) → ((x ≠ P.plane.position a) → ((x ≠
        P.plane.position b) → ((x ∈ closure (P.plane.faceRegion f)) → ((∃ i, P.plane.faceVertex f
        i = a) ∧ (∃ i, P.plane.faceVertex f i = b))))))) → ((∀ (f : P.plane.Face), ∀ (g :
        P.plane.Face), ∀ (x : Real × Real), (x ∈ P.plane.faceRegion f) → ((x ∈ closure
        (P.plane.faceRegion g)) → (f = g))) → (∀ (a : ι), IsOpen (P3776T1OpenStar P
        a))))))))))) := by
  classical
  intro ι P this harc hLF hboundaryEdge hposFace hcover havoid harcMatch hclosureVertex
      hclosureEdge hclosureRegion a
  -- Group the closed nonincident strata by face, so local finiteness is inherited.
  let badVertex (f : P.plane.Face) (i : Fin 3) : Set (Real × Real) :=
    if P.plane.faceVertex f i ≠ a then {P.plane.position (P.plane.faceVertex f i)} else ∅
  let badEdge (f : P.plane.Face) (ij : Fin 3 × Fin 3) : Set (Real × Real) :=
    if ij.1 ≠ ij.2 ∧ P.plane.faceVertex f ij.1 ≠ a ∧
        P.plane.faceVertex f ij.2 ≠ a then
      P.plane.edgeArc (P.plane.faceVertex f ij.1) (P.plane.faceVertex f ij.2) else ∅
  let bad (f : P.plane.Face) : Set (Real × Real) :=
    (if ¬ ∃ i, P.plane.faceVertex f i = a then closure (P.plane.faceRegion f) else ∅) ∪
      (⋃ i, badVertex f i) ∪ ⋃ ij, badEdge f ij
  have hbV (f : P.plane.Face) (i : Fin 3) :
      badVertex f i ⊆ closure (P.plane.faceRegion f) := by
    by_cases h : P.plane.faceVertex f i = a
    · simp [badVertex, h]
    · simpa [badVertex, h] using Set.singleton_subset_iff.mpr (hposFace f i)
  have hbE (f : P.plane.Face) (ij : Fin 3 × Fin 3) :
      badEdge f ij ⊆ closure (P.plane.faceRegion f) := by
    dsimp [badEdge]
    split_ifs with h
    · exact (hboundaryEdge f ij.1 ij.2 h.1).trans frontier_subset_closure
    · exact Set.empty_subset _
  have hbsub (f : P.plane.Face) : bad f ⊆ closure (P.plane.faceRegion f) := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · by_cases hf : ∃ i, P.plane.faceVertex f i = a
      · simp [hf] at hx
      · simpa [hf] using hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hbV f i hi
    · obtain ⟨ij, hij⟩ := Set.mem_iUnion.mp hx
      exact hbE f ij hij
  have hbclosed (f : P.plane.Face) : IsClosed (bad f) := by
    have hc : IsClosed
        (if ¬ ∃ i, P.plane.faceVertex f i = a then closure (P.plane.faceRegion f) else ∅) := by
      by_cases hf : ∃ i, P.plane.faceVertex f i = a
      · simp [hf]
      · simpa only [hf, not_false_eq_true, ↓reduceIte] using
          (isClosed_closure : IsClosed (closure (P.plane.faceRegion f)))
    have hv : IsClosed (⋃ i, badVertex f i) := by
      apply isClosed_iUnion_of_finite
      intro i
      by_cases h : P.plane.faceVertex f i = a
      · simp [badVertex, h]
      · simpa only [badVertex, ite_eq_left h] using
          (isClosed_singleton : IsClosed {P.plane.position (P.plane.faceVertex f i)})
    have he : IsClosed (⋃ ij, badEdge f ij) := by
      apply isClosed_iUnion_of_finite
      intro ij
      dsimp [badEdge]
      split_ifs with h
      · exact (harc _ _ (P.plane.face_edges f ij.1 ij.2 h.1)).isClosed
      · exact isClosed_empty
    exact (hc.union hv).union he
  have hvertexNot (w : ι) (hwa : w ≠ a) :
      P.plane.position w ∉ P3776T1OpenStar P a := by
    rintro (hx | ⟨b, hab, hx, hxa, hxb⟩ | ⟨f, hf, hx⟩)
    · exact hwa (P.plane.position_injective hx)
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 a b hab hx with h | h
      · exact hwa h
      · exact hxb (congrArg P.plane.position h)
    · exact Set.disjoint_left.mp (havoid f) (Or.inl ⟨w, rfl⟩) hx
  have hedgeNot (c d : ι) (hcd : P.plane.adjacent c d)
      (hca : c ≠ a) (hda : d ≠ a) (x : Real × Real)
      (hx : x ∈ P.plane.edgeArc c d) : x ∉ P3776T1OpenStar P a := by
    rintro (hxa | ⟨b, hab, hy, hya, hyb⟩ | ⟨f, hf, hy⟩)
    · rw [hxa] at hx
      rcases (P3767T1VertexEdgeIncidence P.plane a).2 c d hcd hx with h | h
      · exact hca h.symm
      · exact hda h.symm
    · have heq := harcMatch a b c d hab hcd x hy hya hyb hx
      have ha : a ∈ ({c, d} : Set ι) := heq ▸ (by simp)
      rcases Set.mem_insert_iff.mp ha with h | h
      · exact hca h.symm
      · exact hda (Set.mem_singleton_iff.mp h).symm
    · exact Set.disjoint_left.mp (havoid f) (Or.inr ⟨c, d, hcd, hx⟩) hy
  have hbadNot (f : P.plane.Face) : bad f ⊆ (P3776T1OpenStar P a)ᶜ := by
    intro x hx hs
    rcases hx with (hx | hx) | hx
    · have hf : ¬ ∃ i, P.plane.faceVertex f i = a := by
        by_contra h
        simp [h] at hx
      have hxf : x ∈ closure (P.plane.faceRegion f) := by simpa [hf] using hx
      rcases hs with hxa | ⟨b, hab, hx, hxa, hxb⟩ | ⟨g, hga, hxg⟩
      · rw [hxa] at hxf
        exact hf (hclosureVertex f a hxf)
      · exact hf (hclosureEdge f a b hab x hx hxa hxb hxf).1
      · have hgf := hclosureRegion g f x hxg hxf
        exact hf (hgf ▸ hga)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      by_cases h : P.plane.faceVertex f i = a
      · simp [badVertex, h] at hi
      · have hxi : x = P.plane.position (P.plane.faceVertex f i) := by
          simpa [badVertex, h] using hi
        exact hvertexNot _ h (hxi ▸ hs)
    · obtain ⟨ij, hij⟩ := Set.mem_iUnion.mp hx
      dsimp [badEdge] at hij
      split_ifs at hij with h
      · exact hedgeNot _ _ (P.plane.face_edges f ij.1 ij.2 h.1)
          h.2.1 h.2.2 x hij hs
      · exact hij.elim
  have hbadArc (f : P.plane.Face) (i j : Fin 3) (hij : i ≠ j)
      (x : Real × Real)
      (hx : x ∈ P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j))
      (hs : x ∉ P3776T1OpenStar P a) : x ∈ bad f := by
    by_cases hxi : x = P.plane.position (P.plane.faceVertex f i)
    · have hia : P.plane.faceVertex f i ≠ a := by
        intro h
        exact hs (Or.inl (h ▸ hxi))
      apply Or.inl ∘ Or.inr
      exact Set.mem_iUnion.mpr ⟨i, by simp [badVertex, hia, hxi]⟩
    by_cases hxj : x = P.plane.position (P.plane.faceVertex f j)
    · have hja : P.plane.faceVertex f j ≠ a := by
        intro h
        exact hs (Or.inl (h ▸ hxj))
      apply Or.inl ∘ Or.inr
      exact Set.mem_iUnion.mpr ⟨j, by simp [badVertex, hja, hxj]⟩
    have hia : P.plane.faceVertex f i ≠ a := by
      intro h
      apply hs
      right
      left
      exact ⟨P.plane.faceVertex f j, h ▸ P.plane.face_edges f i j hij,
        h ▸ hx, h ▸ hxi, hxj⟩
    have hja : P.plane.faceVertex f j ≠ a := by
      intro h
      apply hs
      right
      left
      refine ⟨P.plane.faceVertex f i, h ▸ P.plane.face_edges f j i hij.symm, ?_, h ▸ hxj, hxi⟩
      rw [P.plane.arc_symmetric]
      simpa only [h] using hx
    right
    exact Set.mem_iUnion.mpr ⟨(i, j), by simp [badEdge, hij, hia, hja, hx]⟩
  have heq : (P3776T1OpenStar P a)ᶜ = ⋃ f, bad f := by
    ext x
    constructor
    · intro hs
      obtain ⟨f, hxf⟩ := hcover x
      apply Set.mem_iUnion.mpr
      refine ⟨f, ?_⟩
      by_cases hf : ∃ i, P.plane.faceVertex f i = a
      · rw [closure_eq_self_union_frontier] at hxf
        rcases hxf with hxr | hxf
        · exact (hs (Or.inr (Or.inr ⟨f, hf, hxr⟩))).elim
        · rw [P.plane.face_boundary] at hxf
          rcases hxf with (hx | hx) | hx
          · exact hbadArc f 0 1 (by decide) x hx hs
          · exact hbadArc f 1 2 (by decide) x hx hs
          · exact hbadArc f 2 0 (by decide) x hx hs
      · exact Or.inl (Or.inl (by simpa [hf] using hxf))
    · intro hx
      obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
      exact hbadNot f hf
  rw [← isClosed_compl_iff, heq]
  exact (hLF.subset hbsub).isClosed_iUnion hbclosed

private theorem hstarcompact :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ [Nontrivial ι], (∀ (f : P.plane.Face),
        IsCompact (closure (P.plane.faceRegion f))) → ((∀ (K : Set (Real × Real)), (IsCompact K)
        → (Set.Finite {f | (K ∩ closure (P.plane.faceRegion f)).Nonempty})) → ((∀ (a : ι), ∀ (b :
        ι), (P.plane.adjacent a b) → (∃ f : P.plane.Face, (∃ i, P.plane.faceVertex f i = a) ∧ (∃
        j, P.plane.faceVertex f j = b) ∧ P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f))) →
        ((∀ (f : P.plane.Face), ∀ (i : Fin 3), P.plane.position (P.plane.faceVertex f i) ∈
        closure (P.plane.faceRegion f)) → (∀ (a : ι), IsCompact (closure (P3776T1OpenStar P
        a)))))) := by
  classical
  intro ι P this hcompact hfiniteFace hedgeFace hposFace a
  have hfiniteInc : Set.Finite {f : P.plane.Face | ∃ i, P.plane.faceVertex f i = a} := by
    apply (hfiniteFace {P.plane.position a} isCompact_singleton).subset
    rintro f ⟨i, hi⟩
    exact ⟨P.plane.position a, rfl, hi ▸ hposFace f i⟩
  let A : Set (Real × Real) :=
    ⋃ f ∈ {f : P.plane.Face | ∃ i, P.plane.faceVertex f i = a},
      closure (P.plane.faceRegion f)
  have hA : IsCompact A := hfiniteInc.isCompact_biUnion (fun f _ => hcompact f)
  have hsub : P3776T1OpenStar P a ⊆ A := by
    intro x hx
    rcases hx with hxa | ⟨b, hab, hx, _, _⟩ | ⟨f, hf, hx⟩
    · obtain ⟨b, hab⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
      obtain ⟨f, ⟨i, hi⟩, _, _⟩ := hedgeFace a b hab
      exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr
        ⟨⟨i, hi⟩, hxa.symm ▸ (hi ▸ hposFace f i)⟩⟩
    · obtain ⟨f, hf, _, hs⟩ := hedgeFace a b hab
      exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hs hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, subset_closure hx⟩⟩
  exact hA.of_isClosed_subset isClosed_closure (closure_minimal hsub hA.isClosed)

private theorem hstarcover :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (x : Real × Real), ∃ a, x ∈ P3776T1OpenStar P a
        := by
  classical
  intro ι P x
  have hx : x ∈ Set.range P.plane.position ∪
      {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ P.plane.edgeArc a b} ∪
      {p | ∃ f, p ∈ P.plane.faceRegion f} := by
    rw [P.plane.plane_cover]
    trivial
  rcases hx with (⟨a, rfl⟩ | ⟨a, b, hab, hx⟩) | ⟨f, hx⟩
  · exact ⟨a, Or.inl rfl⟩
  · by_cases hxa : x = P.plane.position a
    · exact ⟨a, Or.inl hxa⟩
    by_cases hxb : x = P.plane.position b
    · exact ⟨b, Or.inl hxb⟩
    exact ⟨a, Or.inr (Or.inl ⟨b, hab, hx, hxa, hxb⟩)⟩
  · exact ⟨P.plane.faceVertex f 0, Or.inr (Or.inr ⟨f, ⟨0, rfl⟩, hx⟩)⟩

private theorem hstarForward :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : P.lattice), ∀ (a : ι), (fun x => x +
        GaussianRealPoint u) '' P3776T1OpenStar P a ⊆
        P3776T1OpenStar P (P.shift u a) := by
  classical
  intro ι P u a
  rintro x ⟨y, hy, rfl⟩
  rcases hy with hya | ⟨b, hab, hy, hya, hyb⟩ | ⟨f, ⟨i, hi⟩, hy⟩
  · left
    rw [P.position_periodic, hya]
  · right
    left
    refine ⟨P.shift u b, (P.edge_periodic u a b).mpr hab, ?_, ?_, ?_⟩
    · rw [P.edgeArc_periodic]
      exact ⟨y, hy, rfl⟩
    · intro h
      rw [P.position_periodic] at h
      exact hya (add_right_cancel h)
    · intro h
      rw [P.position_periodic] at h
      exact hyb (add_right_cancel h)
  · right
    right
    refine ⟨P.faceShift u f, ⟨i, ?_⟩, ?_⟩
    · rw [P.face_vertices_periodic, hi]
    · rw [P.faceRegion_periodic]
      exact ⟨y, hy, rfl⟩

private theorem hstarPeriodic :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (∀ (u : P.lattice), ∀ (a : ι), (fun x => x +
        GaussianRealPoint u) '' P3776T1OpenStar P a ⊆ P3776T1OpenStar P (P.shift u a)) → (∀
        (u : P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) =
        (fun x => x + GaussianRealPoint u) '' P3776T1OpenStar P a) := by
  classical
  intro ι P hstarForward u a
  apply Set.Subset.antisymm
  · intro x hx
    have hinv : P.shift (-u) (P.shift u a) = a := by
      rw [← P.shift_add]
      simp only [neg_add_cancel, P.shift_zero]
    have hneg : GaussianRealPoint ((-u : P.lattice) : GaussianInt) =
        -GaussianRealPoint (u : GaussianInt) := by
      ext <;> simp [GaussianRealPoint]
    have hy : x + GaussianRealPoint ((-u : P.lattice) : GaussianInt) ∈
        P3776T1OpenStar P a := by
      rw [← hinv]
      exact hstarForward (-u) (P.shift u a) ⟨x, hx, rfl⟩
    refine ⟨x + GaussianRealPoint ((-u : P.lattice) : GaussianInt), hy, ?_⟩
    rw [hneg]
    exact neg_add_cancel_right x (GaussianRealPoint u)
  · exact hstarForward u a

end FixedPeriodicGeometryProof

theorem P3776T1FixedGeometry {ι : Type} (P : PeriodicTileCore ι) :
    Nontrivial ι ∧
    (∀ f, IsCompact (closure (P.plane.faceRegion f))) ∧
    (∀ K : Set (Real × Real), IsCompact K →
      Set.Finite {f | (K ∩ closure (P.plane.faceRegion f)).Nonempty}) ∧
    (∀ x : Real × Real, ∃ f, x ∈ closure (P.plane.faceRegion f)) ∧
    (∀ a, IsOpen (P3776T1OpenStar P a) ∧
      IsCompact (closure (P3776T1OpenStar P a))) ∧
    (∀ x : Real × Real, ∃ a, x ∈ P3776T1OpenStar P a) ∧
    (∀ u : P.lattice, ∀ a,
      P3776T1OpenStar P (P.shift u a) =
        (fun x => x + GaussianRealPoint u) '' P3776T1OpenStar P a) ∧
    (∀ u v : P.lattice, ∀ a, P.shift u a = P.shift v a → u = v) := by
-- BODY
  classical
  have hfree (u v : P.lattice) (a : ι)
      (h : P.shift u a = P.shift v a) : u = v := FixedPeriodicGeometryProof.hfree ι P u v a h
  have hnonzero : ∃ u : P.lattice, u ≠ 0 := FixedPeriodicGeometryProof.hnonzero ι P
  have hinhab : Nonempty ι := FixedPeriodicGeometryProof.hinhab ι P
  have hntriv : Nontrivial ι := by
    obtain ⟨a⟩ := hinhab
    obtain ⟨u, hu⟩ := hnonzero
    refine ⟨⟨P.shift u a, a, ?_⟩⟩
    intro h
    exact hu (hfree u 0 a (h.trans (P.shift_zero a).symm))
  let : Nontrivial ι := hntriv
  have hfacefree (u : P.lattice) (f : P.plane.Face)
      (h : P.faceShift u f = f) : u = 0 := by
    apply hfree u 0 (P.plane.faceVertex f 0)
    rw [P.shift_zero, ← P.face_vertices_periodic, h]
  have harc (a b : ι) (hab : P.plane.adjacent a b) :
      IsCompact (P.plane.edgeArc a b) := FixedPeriodicGeometryProof.harc ι P a b hab
  have hfront (f : P.plane.Face) : IsCompact (frontier (P.plane.faceRegion f)) := by
    rw [P.plane.face_boundary]
    exact ((harc _ _ (P.plane.face_edges f 0 1 (by decide))).union
      (harc _ _ (P.plane.face_edges f 1 2 (by decide)))).union
      (harc _ _ (P.plane.face_edges f 2 0 (by decide)))
  have hexterior (B : Real) : IsPreconnected {x : Real × Real | B < ‖x‖} :=
      FixedPeriodicGeometryProof.hexterior ι P hnonzero B
  have hcompact (f : P.plane.Face) : IsCompact (closure (P.plane.faceRegion f)) :=
      FixedPeriodicGeometryProof.hcompact ι P hnonzero hfacefree hfront hexterior f
  have hfiniteTrans (K A : Set (Real × Real)) (hK : IsCompact K) (hA : IsCompact A) :
      Set.Finite {u : P.lattice |
        (K ∩ (fun x => x + GaussianRealPoint u) '' A).Nonempty} :=
            FixedPeriodicGeometryProof.hfiniteTrans ι P K A hK hA
  have hclosurePeriodic (u : P.lattice) (f : P.plane.Face) :
      closure (P.plane.faceRegion (P.faceShift u f)) =
        (fun x => x + GaussianRealPoint u) '' closure (P.plane.faceRegion f) := by
    rw [P.faceRegion_periodic]
    exact (Homeomorph.addRight (GaussianRealPoint u)).image_closure _ |>.symm
  have hfiniteFace (K : Set (Real × Real)) (hK : IsCompact K) :
      Set.Finite {f | (K ∩ closure (P.plane.faceRegion f)).Nonempty} :=
          FixedPeriodicGeometryProof.hfiniteFace ι P hcompact hfiniteTrans hclosurePeriodic K hK
  have hLF : LocallyFinite (fun f => closure (P.plane.faceRegion f)) := by
    intro x
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num), ?_⟩
    exact (hfiniteFace _ (isCompact_closedBall x 1)).subset
      (fun f ⟨y, hyf, hyK⟩ => ⟨y, hyK, hyf⟩)
  have hendpoints (a b : ι) (hab : P.plane.adjacent a b) :
      P.plane.position a ∈ P.plane.edgeArc a b ∧
        P.plane.position b ∈ P.plane.edgeArc a b := by
    obtain ⟨h, hzero, hone⟩ := P.plane.arc_homeomorph a b hab
    constructor
    · rw [← hzero]
      exact (h ⟨0, by norm_num⟩).property
    · rw [← hone]
      exact (h ⟨1, by norm_num⟩).property
  have hboundaryEdge (f : P.plane.Face) (i j : Fin 3) (hij : i ≠ j) :
      P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆
        frontier (P.plane.faceRegion f) := FixedPeriodicGeometryProof.hboundaryEdge ι P f i j hij
  have hedgeFace (a b : ι) (hab : P.plane.adjacent a b) :
      ∃ f : P.plane.Face,
        (∃ i, P.plane.faceVertex f i = a) ∧
        (∃ j, P.plane.faceVertex f j = b) ∧
        P.plane.edgeArc a b ⊆ closure (P.plane.faceRegion f) :=
            FixedPeriodicGeometryProof.hedgeFace ι P hboundaryEdge a b hab
  have hposFace (f : P.plane.Face) (i : Fin 3) :
      P.plane.position (P.plane.faceVertex f i) ∈ closure (P.plane.faceRegion f) := by
    have hi : ∃ j : Fin 3, i ≠ j := exists_ne i |>.imp (fun _ h => h.symm)
    obtain ⟨j, hij⟩ := hi
    exact frontier_subset_closure (hboundaryEdge f i j hij
      (hendpoints _ _ (P.plane.face_edges f i j hij)).1)
  have hcover (x : Real × Real) : ∃ f, x ∈ closure (P.plane.faceRegion f) :=
      FixedPeriodicGeometryProof.hcoverAt366 ι P  hedgeFace hposFace x
  have havoid (f : P.plane.Face) :
      Disjoint (P3767T1FixedTrace P.plane) (P.plane.faceRegion f) :=
    (P3767T1FixedFaceComponents P.plane).1 f |>.1
  have harcMatch (a b c d : ι) (hab : P.plane.adjacent a b)
      (hcd : P.plane.adjacent c d) (x : Real × Real)
      (hx : x ∈ P.plane.edgeArc a b) (hxa : x ≠ P.plane.position a)
      (hxb : x ≠ P.plane.position b) (hy : x ∈ P.plane.edgeArc c d) :
      ({a, b} : Set ι) = {c, d} := FixedPeriodicGeometryProof.harcMatch ι P a b c d hab hcd x hx
          hxa hxb hy
  have hclosureVertex (f : P.plane.Face) (w : ι)
      (hx : P.plane.position w ∈ closure (P.plane.faceRegion f)) :
      ∃ i, P.plane.faceVertex f i = w := FixedPeriodicGeometryProof.hclosureVertex ι P  havoid f
          w hx
  have hclosureEdge (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b)
      (x : Real × Real) (hx : x ∈ P.plane.edgeArc a b)
      (hxa : x ≠ P.plane.position a) (hxb : x ≠ P.plane.position b)
      (hxf : x ∈ closure (P.plane.faceRegion f)) :
      (∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b) :=
          FixedPeriodicGeometryProof.hclosureEdge ι P havoid harcMatch f a b hab x hx hxa hxb hxf
  have hclosureRegion (f g : P.plane.Face) (x : Real × Real)
      (hx : x ∈ P.plane.faceRegion f) (hy : x ∈ closure (P.plane.faceRegion g)) : f = g := by
    by_contra hne
    exact Set.disjoint_left.mp ((P.plane.region_disjoint hne).closure_right
      (P.plane.region_open f)) hx hy
  have hstaropen (a : ι) : IsOpen (P3776T1OpenStar P a) := FixedPeriodicGeometryProof.hstaropen
      ι P  harc hLF hboundaryEdge hposFace hcover havoid harcMatch hclosureVertex
      hclosureEdge hclosureRegion a
  have hstarcompact (a : ι) : IsCompact (closure (P3776T1OpenStar P a)) :=
      FixedPeriodicGeometryProof.hstarcompact ι P  hcompact hfiniteFace hedgeFace
      hposFace a
  have hstarcover (x : Real × Real) : ∃ a, x ∈ P3776T1OpenStar P a :=
      FixedPeriodicGeometryProof.hstarcover ι P x
  have hstarForward (u : P.lattice) (a : ι) :
      (fun x => x + GaussianRealPoint u) '' P3776T1OpenStar P a ⊆
        P3776T1OpenStar P (P.shift u a) := FixedPeriodicGeometryProof.hstarForward ι P u a
  have hstarPeriodic (u : P.lattice) (a : ι) :
      P3776T1OpenStar P (P.shift u a) =
        (fun x => x + GaussianRealPoint u) '' P3776T1OpenStar P a :=
            FixedPeriodicGeometryProof.hstarPeriodic ι P hstarForward u a
  exact ⟨hntriv, hcompact, hfiniteFace, hcover,
    fun a => ⟨hstaropen a, hstarcompact a⟩, hstarcover, hstarPeriodic, hfree⟩

end ApollonianSuperharmonic

end
