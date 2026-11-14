/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCellEdges

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.PairAssignmentFacts
public import LeanPool.ApollonianSuperharmonic.TileCornerMultiplicity
public import LeanPool.ApollonianSuperharmonic.CircleMatrixSymmetry

public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.QuadraticAffineLaplacian
public import LeanPool.ApollonianSuperharmonic.RealLaplacianLinearity
public import LeanPool.ApollonianSuperharmonic.IntegerLaplacianCastBridge

-- [TABLET NODE: PeriodicTileTotalIndegree]

/-!
# PeriodicTileTotalIndegree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PeriodicIndegreeGeometry

private theorem hordered :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt), ((D.product D).filter fun (e : GaussianInt × GaussianInt) =>
            FourNeighborAdjacent e.1 e.2).card = 2 * ((D.filter fun z => z + 1 ∈ D).card +
            (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card) ) := by
  classical
  intro D
  let I : GaussianInt := ⟨0, 1⟩
  have hstep (s : GaussianInt) :
      ((D.product D).filter fun e => e.2 = e.1 + s).card =
        (D.filter fun z => z + s ∈ D).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨heD, heq⟩
      rcases Finset.mem_product.mp heD with ⟨hfirst, hsecond⟩
      exact Finset.mem_filter.mpr ⟨hfirst, heq ▸ hsecond⟩
    · intro a ha b hb hab
      apply Prod.ext hab
      rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab]
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzD, hzs⟩
      exact ⟨(z, z + s), by simp [hzD, hzs], rfl⟩
  have hreverse (s : GaussianInt) :
      (D.filter fun z => z + (-s) ∈ D).card =
        (D.filter fun z => z + s ∈ D).card := by
    apply Finset.card_bij (fun z _ => z - s)
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzD, hzs⟩
      exact Finset.mem_filter.mpr
        ⟨by simpa [sub_eq_add_neg] using hzs, by simpa using hzD⟩
    · intro a ha b hb hab
      have hab' := congrArg (fun z : GaussianInt => z + s) hab
      simpa using hab'
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzD, hzs⟩
      exact ⟨z + s, by simp [hzD, hzs], by simp⟩
  have hpoint (e : GaussianInt × GaussianInt) :
      (if FourNeighborAdjacent e.1 e.2 then 1 else 0 : Nat) =
        (if e.2 = e.1 + 1 then 1 else 0) +
        (if e.2 = e.1 + (-1) then 1 else 0) +
        (if e.2 = e.1 + I then 1 else 0) +
        (if e.2 = e.1 + (-I) then 1 else 0) := by
    rcases e with ⟨x, y⟩
    simp only [FourNeighborAdjacent, sub_eq_add_neg]
    split_ifs <;> simp_all [I, Zsqrtd.ext_iff]
  have hsum := Finset.sum_congr (s₁ := D.product D) rfl (fun e _ => hpoint e)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [← Finset.card_filter] at hsum
  rw [hstep 1, hstep (-1), hstep I, hstep (-I), hreverse 1, hreverse I] at hsum
  change _ = 2 * ((D.filter fun z => z + 1 ∈ D).card +
    (D.filter fun z => z + I ∈ D).card)
  omega


private theorem hfull_not_boundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), (z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧
            z - 1 - I ∈ T.cells) → (z ∉ BoundaryFootprintVertices T)) ) := by
  classical
  intro T hcells I z hz hb
  rw [BoundaryFootprintVertices, ite_eq_left hcells] at hb
  rcases hb with ⟨e, ⟨w, (⟨rfl, hw⟩ | ⟨rfl, hw⟩)⟩, hze⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hze
    rcases hze with rfl | rfl
    · rcases hw with hw | hw
      · exact hw.2 hz.2.2.1
      · exact hw.1 hz.1
    · have hleft : w + 1 - 1 = w := by ring
      have hlow : w + 1 - 1 - I = w - I := by ring
      rcases hw with hw | hw
      · apply hw.2
        simpa only [hlow, I] using hz.2.2.2
      · apply hw.1
        simpa only [hleft] using hz.2.1
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hze
    rcases hze with rfl | rfl
    · rcases hw with hw | hw
      · exact hw.2 hz.2.1
      · exact hw.1 hz.1
    · have hlow : w + I - I = w := by ring
      have hleft : w + I - 1 - I = w - 1 := by ring
      rcases hw with hw | hw
      · apply hw.2
        simpa only [I, hleft] using hz.2.2.2
      · apply hw.1
        simpa only [I, hlow] using hz.2.2.1

private theorem hN4 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (z : GaussianInt), z ∈ D ↔ z ∈
            FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → ((∀ z ∈ FootprintVertices T,
            z ∉ BoundaryFootprintVertices T → z ∈ T.cells ∧ z - (1 : GaussianInt) ∈ T.cells ∧ z -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ T.cells ∧ z - (1 : GaussianInt) - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ T.cells) → ((T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let N : Nat → Nat := fun k =>
          (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
        (∀ (z : GaussianInt), cornerBag.count z = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
            T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells
            then 1 else 0)) → ((∀ (z : GaussianInt), (z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈
            T.cells ∧ z - 1 - I ∈ T.cells) → (z ∉ BoundaryFootprintVertices T)) → (D.card = N
            4))))) ) := by
  classical
  intro T D hDmem hsectorAll hcells I cornerBag N hcornerCount hfull_not_boundary
  have hs : D = cornerBag.toFinset.filter fun z => cornerBag.count z = 4 := by
    ext z
    rw [hDmem, Finset.mem_filter, hcornerCount]
    constructor
    · rintro ⟨hz, hn⟩
      have hall := hsectorAll z hz hn
      have hzbag : z ∈ cornerBag.toFinset := by
        rw [Multiset.mem_toFinset, Multiset.mem_bind]
        exact ⟨z, hall.1, by simp⟩
      exact ⟨hzbag, by simp only [I] at *; simp [hall.1, hall.2.1, hall.2.2.1, hall.2.2.2]⟩
    · rintro ⟨_, hc⟩
      have hall : z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧
          z - 1 - I ∈ T.cells := by
        by_cases h0 : z ∈ T.cells <;> by_cases h1 : z - 1 ∈ T.cells <;>
          by_cases hI : z - I ∈ T.cells <;> by_cases h1I : z - 1 - I ∈ T.cells <;>
          simp only [h0, h1, hI, h1I, ite_true, ite_false] at hc <;>
          norm_num at hc; exact ⟨h0, h1, hI, h1I⟩
      refine ⟨?_, hfull_not_boundary z hall⟩
      rw [FootprintVertices, ite_eq_left hcells]
      exact ⟨z, hall.1, Or.inl rfl⟩
  exact congrArg Finset.card hs

private theorem hvertex_partition :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let N : Nat → Nat := fun k =>
          (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
        ((4 : ℕ) * Finset.card T.cells = N (1 : ℕ) + (2 : ℕ) * N (2 : ℕ) + (3 : ℕ) * N (3 : ℕ) +
            (4 : ℕ) * N (4 : ℕ) ∧ (FootprintVertices T).ncard = N (1 : ℕ) + N (2 : ℕ) + N (3 : ℕ)
            + N (4 : ℕ) ∧ (2 : ℕ) * (FootprintEdges T).ncard = (4 : ℕ) * Finset.card T.cells +
            (BoundaryFootprintEdges T).ncard ∧ (BoundaryFootprintEdges T).ncard = N (1 : ℕ) + N
            (2 : ℕ) + N (3 : ℕ)) → ((D.card = N 4) → ((FootprintVertices T).ncard = D.card +
            (BoundaryFootprintEdges T).ncard))) ) := by
  classical
  intro T D I cornerBag N hinc hN4
  omega

private abbrev hV :=
  TileCornerMultiplicity.vertexSupport

private theorem hEmem :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        ((V : Set GaussianInt) = FootprintVertices T) → ((∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges T) → (∀ (z : GaussianInt), (z ∈ e) → (z ∈ FootprintVertices T))) → (
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        ∀ (e : GaussianInt × Bool), e ∈ E ↔ edgeOf e ∈ FootprintEdges T)) ) := by
  classical
  intro T I cornerBag edgeOf V hV hEV E e
  change e ∈ ((V.product (Finset.univ : Finset Bool)).filter
    fun q => edgeOf q ∈ FootprintEdges T) ↔ _
  rw [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  simp only [Finset.mem_univ, and_true]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    have hv := hEV (edgeOf e) he e.1 (by rcases e with ⟨z, b⟩; cases b <;> simp [edgeOf])
    change e.1 ∈ (V : Set GaussianInt)
    rw [hV]
    exact hv

private theorem hEset :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        (∀ (e : GaussianInt × Bool), e ∈ E ↔ edgeOf e ∈ FootprintEdges T) → ((E.image edgeOf :
            Set (Finset GaussianInt)) = FootprintEdges T) ) := by
  classical
  intro T I cornerBag edgeOf V E hEmem
  ext e
  change e ∈ E.image edgeOf ↔ e ∈ FootprintEdges T
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hEmem q).mp hq
  · intro he
    have hrep : ∃ q, edgeOf q = e := by
      rcases he with ⟨c, hc, rfl | rfl | rfl | rfl⟩
      · exact ⟨(c, false), rfl⟩
      · exact ⟨(c, true), rfl⟩
      · exact ⟨(c + 1, true), rfl⟩
      · refine ⟨(c + I, false), ?_⟩
        change ({c + I, c + I + 1} : Finset GaussianInt) =
          {c + I, c + 1 + I}
        congr 1; ring
    rcases hrep with ⟨q, hq⟩
    exact ⟨q, (hEmem q).mpr (hq.symm ▸ he), hq⟩

private theorem hEcard :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        (Function.Injective edgeOf) → (
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        ((E.image edgeOf : Set (Finset GaussianInt)) = FootprintEdges T) → (E.card =
            (FootprintEdges T).ncard)) ) := by
  classical
  intro T I cornerBag edgeOf edgeOf_injective V E hEset
  have hh := congrArg Set.ncard hEset
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ edgeOf_injective] at hh
  exact hh

private theorem hBEsub :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        BoundaryFootprintEdges T ⊆ FootprintEdges T ) := by
  classical
  intro T
  let I : GaussianInt := ⟨0, 1⟩
  rintro e ⟨z, (⟨rfl, hz⟩ | ⟨rfl, hz⟩)⟩
  · rcases hz with hz | hz
    · exact ⟨z, hz.1, Or.inl rfl⟩
    · refine ⟨z - I, hz.2, Or.inr (Or.inr (Or.inr ?_))⟩
      simp [I, add_comm, add_left_comm, sub_eq_add_neg]
  · rcases hz with hz | hz
    · exact ⟨z, hz.1, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz.2, Or.inr (Or.inr (Or.inl ?_))⟩
      simp

private theorem hBEset :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        ((E.image edgeOf : Set (Finset GaussianInt)) = FootprintEdges T) →
            ((BoundaryFootprintEdges T ⊆ FootprintEdges T) → (
        let BE := E.filter fun e => edgeOf e ∈ BoundaryFootprintEdges T
        (BE.image edgeOf : Set (Finset GaussianInt)) = BoundaryFootprintEdges T)) ) := by
  classical
  intro T I cornerBag edgeOf V E hEset hBEsub BE
  ext e
  change e ∈ BE.image edgeOf ↔ e ∈ BoundaryFootprintEdges T
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2
  · intro he
    have hf := hBEsub he
    rw [← hEset] at hf
    rcases Finset.mem_image.mp hf with ⟨q, hq, rfl⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, he⟩, rfl⟩

private theorem hBEcard :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        (Function.Injective edgeOf) → (
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let BE := E.filter fun e => edgeOf e ∈ BoundaryFootprintEdges T
        ((BE.image edgeOf : Set (Finset GaussianInt)) = BoundaryFootprintEdges T) → (BE.card =
            (BoundaryFootprintEdges T).ncard)) ) := by
  classical
  intro T I cornerBag edgeOf edgeOf_injective V E BE hBEset
  have hh := congrArg Set.ncard hBEset
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ edgeOf_injective] at hh
  exact hh

private theorem hApart :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let BE := E.filter fun e => edgeOf e ∈ BoundaryFootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        A.card + BE.card = E.card ) := by
  classical
  intro T I cornerBag edgeOf V E BE A
  simpa only [A, BE, not_not] using
    Finset.card_filter_add_card_filter_not (s := E)
      (fun e => edgeOf e ∉ BoundaryFootprintEdges T)

private theorem hEocc :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        (Function.Injective edgeOf) → (
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        (∀ (e : GaussianInt × Bool), e ∈ E ↔ edgeOf e ∈ FootprintEdges T) → (∀ (q : GaussianInt ×
            Bool), q ∈ E ↔ if q.2 then (q.1 ∈ T.cells ∨ q.1 - 1 ∈ T.cells) else (q.1 ∈ T.cells ∨
            q.1 - I ∈ T.cells))) ) := by
  classical
  intro T I cornerBag edgeOf edgeOf_injective V E hEmem q
  rw [hEmem]
  constructor
  · rintro ⟨c, hc, he | he | he | he⟩
    · have hq : q = (c, false) := edgeOf_injective he
      simp [hq, hc]
    · have hq : q = (c, true) := edgeOf_injective he
      simp [hq, hc]
    · have hq : q = (c + 1, true) := edgeOf_injective he
      simp [hq, hc]
    · have he' : edgeOf q = edgeOf (c + I, false) := by
        rw [he]
        change ({c + I, c + 1 + I} : Finset GaussianInt) =
          {c + I, c + I + 1}
        congr 1; ring
      have hq := edgeOf_injective he'
      simp [hq, hc]
  · rcases q with ⟨z, b⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      ] <;> intro hz
    · rcases hz with hz | hz
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        change ({z, z + 1} : Finset GaussianInt) =
          {z - I + I, z - I + 1 + I}
        congr 1 <;> ring
    · rcases hz with hz | hz
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        simp [edgeOf, I]

private theorem hBEocc :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        (Function.Injective edgeOf) → (∀ (q : GaussianInt × Bool), edgeOf q ∈
            BoundaryFootprintEdges T ↔ if q.2 then ((q.1 ∈ T.cells ∧ q.1 - 1 ∉ T.cells) ∨ (q.1 ∉
            T.cells ∧ q.1 - 1 ∈ T.cells)) else ((q.1 ∈ T.cells ∧ q.1 - I ∉ T.cells) ∨ (q.1 ∉
            T.cells ∧ q.1 - I ∈ T.cells))) ) := by
  classical
  intro T I edgeOf edgeOf_injective q
  constructor
  · rintro ⟨z, (⟨he, hz⟩ | ⟨he, hz⟩)⟩
    · have hq : q = (z, false) := edgeOf_injective he
      simpa [hq, I] using hz
    · have hq : q = (z, true) := edgeOf_injective he
      simpa [hq] using hz
  · rcases q with ⟨z, b⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      ] <;> intro hz
    · exact ⟨z, Or.inl ⟨rfl, hz⟩⟩
    · exact ⟨z, Or.inr ⟨rfl, hz⟩⟩

private theorem hshared :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          let I : GaussianInt := ⟨0, 1⟩
          let cornerBag : Multiset GaussianInt :=
            T.cells.1.bind fun c => ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
          let N : Nat → Nat := fun k =>
            (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
          (4 : ℕ) * Finset.card T.cells =
                N (1 : ℕ) + (2 : ℕ) * N (2 : ℕ) + (3 : ℕ) * N (3 : ℕ) +
                  (4 : ℕ) * N (4 : ℕ) ∧
              (FootprintVertices T).ncard =
                  N (1 : ℕ) + N (2 : ℕ) + N (3 : ℕ) + N (4 : ℕ) ∧
                (2 : ℕ) * (FootprintEdges T).ncard =
                    (4 : ℕ) * Finset.card T.cells + (BoundaryFootprintEdges T).ncard ∧
                  (BoundaryFootprintEdges T).ncard = N (1 : ℕ) + N (2 : ℕ) + N (3 : ℕ) →
            let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
              if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
            let V := cornerBag.toFinset
            let E :=
              (V.product (Finset.univ : Finset Bool)).filter fun e =>
                edgeOf e ∈ FootprintEdges T
            let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
            (∀ (q : GaussianInt × Bool),
                q ∈ E ↔
                  if q.2 then q.1 ∈ T.cells ∨ q.1 - 1 ∈ T.cells
                  else q.1 ∈ T.cells ∨ q.1 - I ∈ T.cells) →
              (∀ (q : GaussianInt × Bool),
                  edgeOf q ∈ BoundaryFootprintEdges T ↔
                    if q.2 then
                      q.1 ∈ T.cells ∧ q.1 - 1 ∉ T.cells ∨
                        q.1 ∉ T.cells ∧ q.1 - 1 ∈ T.cells
                    else
                      q.1 ∈ T.cells ∧ q.1 - I ∉ T.cells ∨
                        q.1 ∉ T.cells ∧ q.1 - I ∈ T.cells) →
                ∀ (q : GaussianInt × Bool),
                  q ∈ A →
                    if q.2 then q.1 ∈ T.cells ∧ q.1 - 1 ∈ T.cells
                    else q.1 ∈ T.cells ∧ q.1 - I ∈ T.cells
    )
            := by
  classical
  intro T I cornerBag N hinc edgeOf V E A hEocc hBEocc q hq
  rcases Finset.mem_filter.mp hq with ⟨hqe, hqb⟩
  rw [hEocc] at hqe
  rw [hBEocc] at hqb
  rcases q with ⟨z, b⟩
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    ] at hqe hqb ⊢ <;> tauto

private theorem hhorizontal :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (x : GaussianInt), (x ∈ T.cells) → ((x - I ∈ T.cells) → (OpenLatticeEdge x (x + 1) ⊆
            interior (TileRealization T))) ) := by
  classical
  intro T I x hupper hlower
  let I : GaussianInt := ⟨0, 1⟩
  let R := Set.Ioo (x.re : Real) ((x.re : Real) + 1) ×ˢ
    Set.Ioo ((x.im : Real) - 1) ((x.im : Real) + 1)
  have hopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hsub : R ⊆ TileRealization T := by
    intro p hp
    rcases hp with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    by_cases hside : p.2 ≤ (x.im : Real)
    · apply Set.mem_iUnion.mpr
      refine ⟨x - I, Set.mem_iUnion.mpr ⟨hlower, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      norm_num [I]
      rw [GaussianInt.toComplex_def₂]
      change ((x.re : Real) ≤ p.1 ∧ (x.im : Real) ≤ p.2 + 1) ∧
        (p.1 ≤ (x.re : Real) + 1 ∧ p.2 ≤ (x.im : Real))
      constructor <;> constructor <;> linarith
    · apply Set.mem_iUnion.mpr
      refine ⟨x, Set.mem_iUnion.mpr ⟨hupper, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith
  intro p hp
  apply hopen.subset_interior_iff.mpr hsub
  rcases hp with ⟨t, ht0, ht1, rfl⟩
  norm_num [R, GaussianRealPoint, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> constructor <;> nlinarith

private theorem hvertical :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (x : GaussianInt), (x ∈ T.cells) → ((x - 1 ∈ T.cells) → (OpenLatticeEdge x (x + I) ⊆
            interior (TileRealization T))) ) := by
  classical
  intro T I x hright hleft
  let R := Set.Ioo ((x.re : Real) - 1) ((x.re : Real) + 1) ×ˢ
    Set.Ioo (x.im : Real) ((x.im : Real) + 1)
  have hopen : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hsub : R ⊆ TileRealization T := by
    intro p hp
    rcases hp with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    by_cases hside : p.1 ≤ (x.re : Real)
    · apply Set.mem_iUnion.mpr
      refine ⟨x - 1, Set.mem_iUnion.mpr ⟨hleft, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      norm_num
      rw [GaussianInt.toComplex_def₂]
      change ((x.re : Real) ≤ p.1 + 1 ∧ (x.im : Real) ≤ p.2) ∧
        (p.1 ≤ (x.re : Real) ∧ p.2 ≤ (x.im : Real) + 1)
      constructor <;> constructor <;> linarith
    · apply Set.mem_iUnion.mpr
      refine ⟨x, Set.mem_iUnion.mpr ⟨hright, ?_⟩⟩
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor <;> constructor <;> linarith
  intro p hp
  apply hopen.subset_interior_iff.mpr hsub
  rcases hp with ⟨t, ht0, ht1, rfl⟩
  norm_num [R, GaussianRealPoint, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> constructor <;> nlinarith

private theorem hedgeOf :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let step : Bool → GaussianInt := fun b => if b then I else 1
        ∀ (q : GaussianInt × Bool), edgeOf q = {q.1, q.1 + step q.2} ) := by
  classical
  intro I edgeOf step q
  rcases q with ⟨z, b⟩
  cases b <;> rfl

private theorem hAendpoint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (z : GaussianInt), z ∈ D ↔ z ∈
            FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → (((∀ (x : LatticeCell), ∀ (y
            : LatticeCell), FourNeighborAdjacent x y → x ∈ BoundaryFootprintVertices T → y ∈
            BoundaryFootprintVertices T → ¬OpenLatticeEdge x y ⊆ interior (TileRealization T)) ∧
            (∀ x ∈ FootprintVertices T, ∀ y ∈ FootprintVertices T, FourNeighborAdjacent x y → {x,
            y} ∈ FootprintEdges T) ∧ ∀ x ∈ FootprintVertices T, GaussianRealPoint x ∈ interior
            (TileRealization T) ↔ x ∉ BoundaryFootprintVertices T) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∀ (z : GaussianInt), (z ∈ e) → (z
            ∈ FootprintVertices T))) → (
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        (∀ (e : GaussianInt × Bool), e ∈ E ↔ edgeOf e ∈ FootprintEdges T) → (
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        (∀ (q : GaussianInt × Bool), (q ∈ A) → (if q.2 then (q.1 ∈ T.cells ∧ q.1 - 1 ∈ T.cells)
            else (q.1 ∈ T.cells ∧ q.1 - I ∈ T.cells))) → ((∀ (x : GaussianInt), (x ∈ T.cells) →
            ((x - I ∈ T.cells) → (OpenLatticeEdge x (x + 1) ⊆ interior (TileRealization T)))) →
            ((∀ (x : GaussianInt), (x ∈ T.cells) → ((x - 1 ∈ T.cells) → (OpenLatticeEdge x (x +
            I) ⊆ interior (TileRealization T)))) → (
        let step : Bool → GaussianInt := fun b => if b then I else 1
        (∀ (q : GaussianInt × Bool), edgeOf q = {q.1, q.1 + step q.2}) → (∀ (q : GaussianInt ×
            Bool), (q ∈ A) → (q.1 ∈ D ∨ q.1 + step q.2 ∈ D))))))))) ) := by
  classical
  intro T D hDmem hreg I cornerBag edgeOf V hEV E hEmem A hshared hhorizontal hvertical step
      hedgeOf q hq
  have hqe := (Finset.mem_filter.mp hq).1
  have hf := (hEmem q).mp hqe
  have hv0 := hEV (edgeOf q) hf q.1 (by rw [hedgeOf]; simp)
  have hv1 := hEV (edgeOf q) hf (q.1 + step q.2) (by rw [hedgeOf]; simp)
  by_contra hn
  have hb0 : q.1 ∈ BoundaryFootprintVertices T := by
    by_contra hb
    exact hn (Or.inl ((hDmem _).mpr ⟨hv0, hb⟩))
  have hb1 : q.1 + step q.2 ∈ BoundaryFootprintVertices T := by
    by_contra hb
    exact hn (Or.inr ((hDmem _).mpr ⟨hv1, hb⟩))
  have hocc := hshared q hq
  rcases q with ⟨z, b⟩
  cases b
  · exact hreg.1 z (z + 1) (Or.inl rfl) hb0 hb1
      (hhorizontal z hocc.1 hocc.2)
  · exact hreg.1 z (z + I) (Or.inr (Or.inr (Or.inl rfl))) hb0 hb1
      (hvertical z hocc.1 hocc.2)

private theorem hDedge_nonboundary :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (z : GaussianInt), z ∈ D ↔ z ∈
            FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → ((T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        ∀ (q : GaussianInt × Bool), ∀ (x : GaussianInt), (x ∈ D) → ((x ∈ edgeOf q) → (edgeOf q ∉
            BoundaryFootprintEdges T)))) ) := by
  classical
  intro T D hDmem hcells I edgeOf q x hx hxe he
  apply (hDmem x).mp hx |>.2
  rw [BoundaryFootprintVertices, ite_eq_left hcells]
  exact ⟨edgeOf q, he, hxe⟩

private theorem hdegree :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (z : GaussianInt), z ∈ D ↔ z ∈
            FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → ((∀ z ∈ FootprintVertices T,
            z ∉ BoundaryFootprintVertices T → z ∈ T.cells ∧ z - (1 : GaussianInt) ∈ T.cells ∧ z -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ T.cells ∧ z - (1 : GaussianInt) - (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ∈ T.cells) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        (∀ (q : GaussianInt × Bool), q ∈ E ↔ if q.2 then (q.1 ∈ T.cells ∨ q.1 - 1 ∈ T.cells) else
            (q.1 ∈ T.cells ∨ q.1 - I ∈ T.cells)) → ((∀ (q : GaussianInt × Bool), ∀ (x :
            GaussianInt), (x ∈ D) → ((x ∈ edgeOf q) → (edgeOf q ∉ BoundaryFootprintEdges T))) →
            (∀ (x : GaussianInt), (x ∈ D) → ((A.filter fun q => x ∈ edgeOf q).card = 4))))) ) := by
  classical
  intro T D hDmem hsectorAll I cornerBag edgeOf V E A hEocc hDedge_nonboundary x hx
  have hall := hsectorAll x ((hDmem x).mp hx).1 ((hDmem x).mp hx).2
  let F : Finset (GaussianInt × Bool) :=
    {(x, false), (x - 1, false), (x, true), (x - I, true)}
  have hs : A.filter (fun q => x ∈ edgeOf q) = F := by
    ext q
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hxq⟩
      rcases q with ⟨z, b⟩
      cases b
      · change x ∈ ({z, z + 1} : Finset GaussianInt) at hxq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxq
        rcases hxq with rfl | rfl <;> simp [F]
      · change x ∈ ({z, z + I} : Finset GaussianInt) at hxq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxq
        rcases hxq with rfl | rfl <;> simp [F]
    · intro hq
      have hxq : x ∈ edgeOf q := by
        simp only [F, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> simp [edgeOf]
      refine ⟨Finset.mem_filter.mpr ⟨?_, hDedge_nonboundary q x hx hxq⟩, hxq⟩
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      all_goals simp [hEocc, I, hall.1, hall.2.1, hall.2.2.1]
  rw [hs]
  have hre : x.re ≠ x.re - 1 := by omega
  have him : x.im ≠ x.im - 1 := by omega
  simp [F, I, Zsqrtd.ext_iff, hre, him]

private theorem hendSum :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let step : Bool → GaussianInt := fun b => if b then I else 1
        (∀ (q : GaussianInt × Bool), edgeOf q = {q.1, q.1 + step q.2}) → (∀ (q : GaussianInt ×
            Bool), (∑ x ∈ D, if x ∈ edgeOf q then 1 else 0 : Nat) = (if q.1 ∈ D then 1 else 0) +
            (if q.1 + step q.2 ∈ D then 1 else 0)) ) := by
  classical
  intro D I edgeOf step hedgeOf q
  have hn : q.1 ≠ q.1 + step q.2 := by
    rcases q with ⟨z, b⟩
    cases b <;> simp [step, I, Zsqrtd.ext_iff]
  have hpoint (x : GaussianInt) :
      (if x ∈ edgeOf q then 1 else 0 : Nat) =
      (if x = q.1 then 1 else 0) +
        (if x = q.1 + step q.2 then 1 else 0) := by
    rw [hedgeOf]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h0 : x = q.1
    · subst x
      simp only [hn, ite_false, ite_true, true_or]
    · by_cases h1 : x = q.1 + step q.2 <;>
        simp only [h0, h1, Ne.symm hn, ite_true, ite_false, or_true, or_false, zero_add,
            add_zero]
  calc
    _ = ∑ x ∈ D, ((if x = q.1 then 1 else 0) +
        (if x = q.1 + step q.2 then 1 else 0)) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

private theorem hdegree_sum :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        let step : Bool → GaussianInt := fun b => if b then I else 1
        (∀ (x : GaussianInt), (x ∈ D) → ((A.filter fun q => x ∈ edgeOf q).card = 4)) → ((∀ (q :
            GaussianInt × Bool), (∑ x ∈ D, if x ∈ edgeOf q then 1 else 0 : Nat) = (if q.1 ∈ D
            then 1 else 0) + (if q.1 + step q.2 ∈ D then 1 else 0)) → ((∑ q ∈ A, ((if q.1 ∈ D
            then 1 else 0) + (if q.1 + step q.2 ∈ D then 1 else 0)) : Nat) = 4 * D.card)) ) := by
  classical
  intro T D I cornerBag edgeOf V E A step hdegree hendSum
  calc
    _ = ∑ q ∈ A, ∑ x ∈ D, if x ∈ edgeOf q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (hendSum q).symm
    _ = ∑ x ∈ D, ∑ q ∈ A, if x ∈ edgeOf q then 1 else 0 := Finset.sum_comm
    _ = ∑ x ∈ D, 4 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_filter]
      exact hdegree x hx
    _ = _ := by simp [Nat.mul_comm]

private theorem hdegree_count :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        let step : Bool → GaussianInt := fun b => if b then I else 1
        (∀ (q : GaussianInt × Bool), (q ∈ A) → (q.1 ∈ D ∨ q.1 + step q.2 ∈ D)) → (((∑ q ∈ A, ((if
            q.1 ∈ D then 1 else 0) + (if q.1 + step q.2 ∈ D then 1 else 0)) : Nat) = 4 * D.card) → (
        let J := A.filter fun q => q.1 ∈ D ∧ q.1 + step q.2 ∈ D
        A.card + J.card = 4 * D.card)) ) := by
  classical
  intro T D I cornerBag edgeOf V E A step hAendpoint hdegree_sum J
  have hp (q : GaussianInt × Bool) (hq : q ∈ A) :
      ((if q.1 ∈ D then 1 else 0) +
        (if q.1 + step q.2 ∈ D then 1 else 0) : Nat) =
      1 + (if q.1 ∈ D ∧ q.1 + step q.2 ∈ D then 1 else 0) := by
    rcases hAendpoint q hq with h0 | h1
    · by_cases h1 : q.1 + step q.2 ∈ D <;> simp [h0, h1]
    · by_cases h0 : q.1 ∈ D <;> simp [h0, h1]
  have hs := Finset.sum_congr (s₁ := A) rfl hp
  rw [hdegree_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    mul_one, ← Finset.card_filter] at hs
  exact hs.symm

private theorem hJmem :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt), (∀ (z : GaussianInt), z ∈ D ↔ z ∈
            FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → (((∀ (x : LatticeCell), ∀ (y
            : LatticeCell), FourNeighborAdjacent x y → x ∈ BoundaryFootprintVertices T → y ∈
            BoundaryFootprintVertices T → ¬OpenLatticeEdge x y ⊆ interior (TileRealization T)) ∧
            (∀ x ∈ FootprintVertices T, ∀ y ∈ FootprintVertices T, FourNeighborAdjacent x y → {x,
            y} ∈ FootprintEdges T) ∧ ∀ x ∈ FootprintVertices T, GaussianRealPoint x ∈ interior
            (TileRealization T) ↔ x ∉ BoundaryFootprintVertices T) → (
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        (∀ (e : GaussianInt × Bool), e ∈ E ↔ edgeOf e ∈ FootprintEdges T) → (
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        let step : Bool → GaussianInt := fun b => if b then I else 1
        (∀ (q : GaussianInt × Bool), edgeOf q = {q.1, q.1 + step q.2}) → ((∀ (q : GaussianInt ×
            Bool), ∀ (x : GaussianInt), (x ∈ D) → ((x ∈ edgeOf q) → (edgeOf q ∉
            BoundaryFootprintEdges T))) → (
        let J := A.filter fun q => q.1 ∈ D ∧ q.1 + step q.2 ∈ D
        ∀ (q : GaussianInt × Bool), q ∈ J ↔ q.1 ∈ D ∧ q.1 + step q.2 ∈ D))))) ) := by
  classical
  intro T D hDmem hreg I cornerBag edgeOf V E hEmem A step hedgeOf hDedge_nonboundary J q
  constructor
  · intro hq
    exact (Finset.mem_filter.mp hq).2
  · rintro ⟨h0, h1⟩
    have he : edgeOf q ∈ FootprintEdges T := by
      rw [hedgeOf]
      apply hreg.2.1 q.1 ((hDmem _).mp h0).1
        (q.1 + step q.2) ((hDmem _).mp h1).1
      rcases q with ⟨z, b⟩
      cases b
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hb := hDedge_nonboundary q q.1 h0 (by rw [hedgeOf]; simp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hEmem q).mpr he, hb⟩,
      h0, h1⟩

private theorem hJset :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        let step : Bool → GaussianInt := fun b => if b then I else 1
        let J := A.filter fun q => q.1 ∈ D ∧ q.1 + step q.2 ∈ D
        (∀ (q : GaussianInt × Bool), q ∈ J ↔ q.1 ∈ D ∧ q.1 + step q.2 ∈ D) → (
        let east := D.filter fun z => z + 1 ∈ D
        let north := D.filter fun z => z + I ∈ D
        J = (east.product {false}) ∪ (north.product {true})) ) := by
  classical
  intro T D I cornerBag edgeOf V E A step J hJmem east north
  ext q
  rw [hJmem]
  rcases q with ⟨z, b⟩
  cases b <;> simp [east, north, step, Finset.product_eq_sprod]

private theorem hdisj :
    (by
      classical
      exact
        ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let east := D.filter fun z => z + 1 ∈ D
        let north := D.filter fun z => z + I ∈ D
        Disjoint (east.product {false}) (north.product {true}) ) := by
  classical
  intro D I east north
  apply Finset.disjoint_left.mpr
  intro q hq hn
  have h0 : q.2 = false := Finset.mem_singleton.mp (Finset.mem_product.mp hq).2
  have h1 : q.2 = true := Finset.mem_singleton.mp (Finset.mem_product.mp hn).2
  exact Bool.false_ne_true (h0.symm.trans h1)

private theorem hJcard :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (D : Finset GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
          ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
        let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
          if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
        let V := cornerBag.toFinset
        let E := (V.product (Finset.univ : Finset Bool)).filter
          fun e => edgeOf e ∈ FootprintEdges T
        let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
        let step : Bool → GaussianInt := fun b => if b then I else 1
        let J := A.filter fun q => q.1 ∈ D ∧ q.1 + step q.2 ∈ D
        let east := D.filter fun z => z + 1 ∈ D
        let north := D.filter fun z => z + I ∈ D
        (J = (east.product {false}) ∪ (north.product {true})) → ((Disjoint (east.product {false})
            (north.product {true})) → (J.card = east.card + north.card)) ) := by
  classical
  intro T D I cornerBag edgeOf V E A step J east north hJset hdisj
  rw [hJset, Finset.card_union_of_disjoint hdisj]
  simp [Finset.product_eq_sprod]

private theorem hboundary_card :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (p : List GaussianInt), (p.Nodup) → ((BoundaryFootprintVertices T =
            (↑p.toFinset : Set GaussianInt)) → ((BoundaryFootprintVertices T).ncard = p.length))
            ) := by
  classical
  intro T p hpnd hverts
  rw [hverts]
  rw [Set.ncard_coe_finset]
  exact List.toFinset_card_of_nodup hpnd

private theorem hDmem :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ((↑h.domain : Set GaussianInt) =
            FootprintVertices T) → (
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        ∀ (z : GaussianInt), z ∈ D ↔ z ∈ FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) )
            := by
  classical
  intro T h hdom D z
  rw [Finset.mem_filter]
  have hdec : @decide (z ∉ BoundaryFootprintVertices T)
      (Classical.propDecidable _) = true ↔
        z ∉ BoundaryFootprintVertices T := by
    cases Classical.propDecidable _ <;> simp
  rw [hdec]
  have hzdom : z ∈ h.domain ↔ z ∈ FootprintVertices T := by
    change z ∈ (h.domain : Set GaussianInt) ↔ z ∈ FootprintVertices T
    rw [hdom]
  rw [hzdom]

private theorem htranslation_rigid :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          T.cells.Nonempty →
            ∀ (v : GaussianInt), (T.cells.image fun z => z + v) = T.cells → v = 0
    ) := by
  classical
  intro T hcells v hs
  have hinj : Function.Injective (fun z : GaussianInt => z + v) := by
    intro a b hab
    exact add_right_cancel hab
  have hsumRe : (∑ z ∈ T.cells, z.re) =
      ∑ z ∈ T.cells, (z + v).re := by
    calc
      _ = ∑ z ∈ T.cells.image (fun z => z + v), z.re := by rw [hs]
      _ = ∑ z ∈ T.cells, (z + v).re :=
        Finset.sum_image (fun a ha b hb hab => hinj hab)
  have hsumIm : (∑ z ∈ T.cells, z.im) =
      ∑ z ∈ T.cells, (z + v).im := by
    calc
      _ = ∑ z ∈ T.cells.image (fun z => z + v), z.im := by rw [hs]
      _ = ∑ z ∈ T.cells, (z + v).im :=
        Finset.sum_image (fun a ha b hb hab => hinj hab)
  have hre : (T.cells.card : ℤ) * v.re = 0 := by
    have hformula : (∑ z ∈ T.cells, (z + v).re) =
        (∑ z ∈ T.cells, z.re) + (T.cells.card : ℤ) * v.re := by
      calc
        _ = ∑ z ∈ T.cells, (z.re + v.re) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact Zsqrtd.re_add z v
        _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
    rw [hformula] at hsumRe
    omega
  have him : (T.cells.card : ℤ) * v.im = 0 := by
    have hformula : (∑ z ∈ T.cells, (z + v).im) =
        (∑ z ∈ T.cells, z.im) + (T.cells.card : ℤ) * v.im := by
      calc
        _ = ∑ z ∈ T.cells, (z.im + v.im) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact Zsqrtd.im_add z v
        _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
    rw [hformula] at hsumIm
    omega
  have hcard : (T.cells.card : ℤ) ≠ 0 := by
    have : 0 < T.cells.card := Finset.card_pos.mpr hcells
    omega
  have hr : v.re = 0 := (mul_eq_zero.mp hre).resolve_left hcard
  have hi : v.im = 0 := (mul_eq_zero.mp him).resolve_left hcard
  ext <;> simp [hr, hi]

private theorem hcell_cover :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (ExactTileTiling (RegularTileFamily T
            (TilingLattice C))) → (∀ (z : GaussianInt), ∃ a ∈ T.cells, ∃ v ∈ TilingLattice C, z =
            a + v) ) := by
  classical
  intro C T htile z
  obtain ⟨U, hU, hzU, _⟩ := htile.2 z
  rcases hU with ⟨v, hv, rfl⟩
  change z ∈ T.cells.image (fun a => a + v) at hzU
  rcases Finset.mem_image.mp hzU with ⟨a, ha, haz⟩
  exact ⟨a, ha, v, hv, haz.symm⟩

private theorem hcell_residue_unique :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (T : ProtoTile),
            ∀ (h : PartialOdometer),
              ∀ (g : IntegerLatticeFunction),
                (↑h.domain : Set GaussianInt) = FootprintVertices T →
                  ExactTileTiling (RegularTileFamily T (TilingLattice C)) →
                    (∀ x ∈ BoundaryFootprintVertices T,
                        FourNeighborLaplacian g x = (1 : ℤ)) →
                      (FootprintVertices T).ncard + Finset.card T.cells =
                          (FootprintEdges T).ncard + (1 : ℕ) →
                        ∀ (p : List GaussianInt),
                          ∀ (x₀ : GaussianInt),
                            ∀ (x₁ : GaussianInt),
                              BoundaryFootprintVertices T =
                                (↑p.toFinset : Set GaussianInt) →
                                (∀ (e : Finset GaussianInt),
                                e ∈ BoundaryFootprintEdges T ↔
                                e = { x₁, x₀ } ∨
                                ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
                                List GaussianInt) (l₂ : List GaussianInt),
                                p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }) →
                                (BoundaryFootprintVertices T).ncard = p.length →
                                (∀ (v : GaussianInt),
                                (T.cells.image fun z => z + v) = T.cells → v = 0) →
                                (∀ (z : GaussianInt),
                                ∃ a ∈ T.cells, ∃ v ∈ TilingLattice C, z = a + v) →
                                ∀ (a : GaussianInt),
                                ∀ (a' : GaussianInt),
                                a ∈ T.cells →
                                a' ∈ T.cells → a - a' ∈ TilingLattice C → a = a'
    ) := by
  classical
  intro C T h g hdom htile hweb heuler p x₀ x₁ hverts hedges hboundary_card htranslation_rigid
      hcell_cover a a' ha ha' hres
  let v := a - a'
  have htransmem : a ∈ (TileTranslation T v).cells := by
    change a ∈ T.cells.image (fun z => z + v)
    exact Finset.mem_image.mpr ⟨a', ha', by dsimp [v]; simp⟩
  have hTmem : T ∈ RegularTileFamily T (TilingLattice C) := by
    refine ⟨0, (TilingLattice C).zero_mem, ?_⟩
    cases T with
    | mk cells anchor =>
      change ({ cells := cells, anchor := anchor } : ProtoTile) =
        { cells := cells.image (fun z => z + 0), anchor := anchor + 0 }
      simp
  have hVmem : TileTranslation T v ∈ RegularTileFamily T (TilingLattice C) :=
    ⟨v, hres, rfl⟩
  obtain ⟨U, hUmem, haU, huniq⟩ := htile.2 a
  have hTU : T = U := huniq T hTmem ha
  have hVU : TileTranslation T v = U := huniq (TileTranslation T v) hVmem htransmem
  have htilesame : TileTranslation T v = T := hVU.trans hTU.symm
  have hcellsame : T.cells.image (fun z => z + v) = T.cells := by
    change T.cells.image (GaussianTranslation v) = T.cells
    exact congrArg ProtoTile.cells htilesame
  change T.cells.image (fun z => z + v) = T.cells at hcellsame
  have hvzero : v = 0 := htranslation_rigid v hcellsame
  dsimp [v] at hvzero
  exact sub_eq_zero.mp hvzero

private theorem hfund :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (∀ (z : GaussianInt), ∃ a ∈ T.cells, ∃ v ∈
            TilingLattice C, z = a + v) → ((∀ (a : GaussianInt), ∀ (a' : GaussianInt), (a ∈
            T.cells) → ((a' ∈ T.cells) → ((a - a' ∈ TilingLattice C) → (a = a')))) →
            (LatticeFundamentalSet (TilingLattice C) T.cells)) ) := by
  classical
  intro C T hcell_cover hcell_residue_unique z
  obtain ⟨a, ha, v, hv, hz⟩ := hcell_cover z
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · rw [hz]
    simpa using hv
  · intro a' ha'
    have hzmem : z - a ∈ TilingLattice C := by
      simpa [hz, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hv
    have hd := (TilingLattice C).sub_mem ha'.2 hzmem
    exact (hcell_residue_unique a a' ha ha'.1
      (by convert hd using 1; abel)).symm

private theorem hcell_card :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (∀ (a : GaussianInt), ∀ (a' : GaussianInt), (a ∈
            T.cells) → ((a' ∈ T.cells) → ((a - a' ∈ TilingLattice C) → (a = a')))) →
            ((LatticeFundamentalSet (TilingLattice C) T.cells) → (∀ (R : Finset GaussianInt),
            (LatticeFundamentalSet (TilingLattice C) R) → (T.cells.card = R.card))) ) := by
  classical
  intro C T hcell_residue_unique hfund R hR
  apply Finset.card_bij
    (fun a _ => Classical.choose (hR a))
  · intro a ha
    exact (Classical.choose_spec (hR a)).1.1
  · intro a ha a' ha' heq
    have hfa := (Classical.choose_spec (hR a)).1.2
    have hfa' := (Classical.choose_spec (hR a')).1.2
    have hfa'' : a' - Classical.choose (hR a) ∈ TilingLattice C := by
      convert hfa' using 1
      rw [heq]
    have hd : a - a' ∈ TilingLattice C := by
      have hs := (TilingLattice C).add_mem hfa
        ((TilingLattice C).neg_mem hfa'')
      convert hs using 1; abel
    exact hcell_residue_unique a a' ha ha' hd
  · intro b hb
    obtain ⟨a, ⟨ha, hba⟩, _⟩ := hfund b
    have haR : a - Classical.choose (hR a) ∈ TilingLattice C :=
      (Classical.choose_spec (hR a)).1.2
    have hbRep : b - Classical.choose (hR a) ∈ TilingLattice C := by
      have hsum := (TilingLattice C).add_mem hba haR
      convert hsum using 1; abel
    have hchoose : Classical.choose (hR a) =
        Classical.choose (hR b) := by
      exact (Classical.choose_spec (hR b)).2 _
        ⟨(Classical.choose_spec (hR a)).1.1, hbRep⟩
    have hbchoose : Classical.choose (hR b) = b := by
      exact ((Classical.choose_spec (hR b)).2 b ⟨hb, by simp⟩).symm
    exact ⟨a, ha, hchoose.trans hbchoose⟩

private theorem hcell_curv :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (R : Finset GaussianInt), (R.card =
            C.1.1.1.natAbs) → ((T.cells.card = R.card) → (T.cells.card = C.1.1.1.natAbs)) ) := by
  classical
  intro C T R hRcard hcell_card
  rw [hcell_card]
  exact hRcard

private theorem hstatusRight :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (
        ∀ (z : GaussianInt), (z ∉ BoundaryFootprintVertices T) → ((z ∈ T.cells ↔ z - 1 ∈
            T.cells))) ) := by
  classical
  intro T hcells z hz
  let I : GaussianInt := ⟨0, 1⟩
  constructor
  · intro hz0
    by_contra hz1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z, z + I}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    exact ⟨z, Or.inr ⟨by simp [I], Or.inl ⟨hz0, hz1⟩⟩⟩
  · intro hz0
    by_contra hz1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z, z + I}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    exact ⟨z, Or.inr ⟨by simp [I], Or.inr ⟨hz1, hz0⟩⟩⟩

private theorem hstatusDown :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), (z ∉ BoundaryFootprintVertices T) → ((z - I ∈ T.cells ↔ z - 1 - I ∈
            T.cells))) ) := by
  classical
  intro T hcells I z hz
  constructor
  · intro h0
    by_contra h1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z - I, z}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    refine ⟨z - I, Or.inr ⟨by simp [I], ?_⟩⟩
    exact Or.inl ⟨by simpa [I, Zsqrtd.ext_iff] using h0,
      by
        have heq : z - I - 1 = z - 1 - I := by ring
        rw [heq]
        exact h1⟩
  · intro h0
    by_contra h1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z - I, z}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    refine ⟨z - I, Or.inr ⟨by simp [I], ?_⟩⟩
    exact Or.inr ⟨by simpa [I, Zsqrtd.ext_iff] using h1,
      by
        have heq : z - I - 1 = z - 1 - I := by ring
        rw [heq]
        exact h0⟩

private theorem hstatusLeft :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), (z ∉ BoundaryFootprintVertices T) → ((z - 1 ∈ T.cells ↔ z - 1 - I ∈
            T.cells))) ) := by
  classical
  intro T hcells I z hz
  constructor
  · intro h0
    by_contra h1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z - 1, z}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    refine ⟨z - 1, Or.inl ⟨by simp, ?_⟩⟩
    exact Or.inl ⟨by simpa [I, Zsqrtd.ext_iff] using h0,
      by simpa [I, Zsqrtd.ext_iff] using h1⟩
  · intro h0
    by_contra h1
    apply hz
    rw [BoundaryFootprintVertices, ite_eq_left hcells]
    refine ⟨{z - 1, z}, ?_, by simp⟩
    rw [BoundaryFootprintEdges]
    refine ⟨z - 1, Or.inl ⟨by simp, ?_⟩⟩
    exact Or.inr ⟨by simpa [I, Zsqrtd.ext_iff] using h1,
      by simpa [I, Zsqrtd.ext_iff] using h0⟩

private theorem hsomeSector :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), (z ∈ FootprintVertices T) → (z ∈ T.cells ∨ z - 1 ∈ T.cells ∨ z - I ∈
            T.cells ∨ z - 1 - I ∈ T.cells)) ) := by
  classical
  intro T hcells I z hz
  rw [FootprintVertices, ite_eq_left hcells] at hz
  rcases hz with ⟨a, ha, rfl | h | h | h⟩
  · exact Or.inl ha
  · right
    left
    simpa [h, sub_eq_add_neg] using ha
  · right
    right
    left
    simpa [h, I, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using ha
  · right
    right
    right
    simpa [h, I, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using ha

private theorem hsectorAll :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (z : GaussianInt), (z ∉ BoundaryFootprintVertices T) → ((z ∈ T.cells ↔ z - 1 ∈
            T.cells))) → ((∀ (z : GaussianInt), (z ∉ BoundaryFootprintVertices T) → ((z - I ∈
            T.cells ↔ z - 1 - I ∈ T.cells))) → ((∀ (z : GaussianInt), (z ∉
            BoundaryFootprintVertices T) → ((z - 1 ∈ T.cells ↔ z - 1 - I ∈ T.cells))) → ((∀ (z :
            GaussianInt), (z ∈ FootprintVertices T) → (z ∈ T.cells ∨ z - 1 ∈ T.cells ∨ z - I ∈
            T.cells ∨ z - 1 - I ∈ T.cells)) → (∀ (z : GaussianInt), (z ∈ FootprintVertices T) →
            ((z ∉ BoundaryFootprintVertices T) → (z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells
            ∧ z - 1 - I ∈ T.cells)))))) ) := by
  classical
  intro T I hstatusRight hstatusDown hstatusLeft hsomeSector z hz hn
  have hr := hstatusRight z hn
  have hd := hstatusDown z hn
  have hl := hstatusLeft z hn
  rcases hsomeSector z hz with h0 | h1 | h2 | h3
  · exact ⟨h0, hr.mp h0, hd.mpr (hl.mp (hr.mp h0)), hl.mp (hr.mp h0)⟩
  · exact ⟨hr.mpr h1, h1, hd.mpr (hl.mp h1), hl.mp h1⟩
  · exact ⟨hr.mpr (hl.mpr (hd.mp h2)), hl.mpr (hd.mp h2), h2, hd.mp h2⟩
  · exact ⟨hr.mpr (hl.mpr h3), hl.mpr h3, hd.mpr h3, h3⟩

private theorem hcellBaseFV :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (∀ (z : GaussianInt), (z ∈ T.cells) → (z ∈
            FootprintVertices T)) ) := by
  classical
  intro T hcells z hz
  rw [FootprintVertices, ite_eq_left hcells]
  exact ⟨z, hz, Or.inl rfl⟩

private theorem hDcells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        (∀ (z : GaussianInt), z ∈ D ↔ z ∈ FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T) → (
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (z : GaussianInt), (z ∈ FootprintVertices T) → ((z ∉ BoundaryFootprintVertices T) → (z
            ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - I ∈ T.cells ∧ z - 1 - I ∈ T.cells))) → ((∀ (z :
            GaussianInt), (z ∈ T.cells) → (z ∈ FootprintVertices T)) → (∀ (z : GaussianInt), z ∈
            D ↔ z ∈ T.cells ∧ z ∉ BoundaryFootprintVertices T))) ) := by
  classical
  intro T h D hDmem I hsectorAll hcellBaseFV z
  constructor
  · intro hz
    rcases hDmem z |>.mp hz with ⟨hzv, hzb⟩
    exact ⟨(hsectorAll z hzv hzb).1, hzb⟩
  · rintro ⟨hzc, hzb⟩
    apply hDmem z |>.mpr
    exact ⟨hcellBaseFV z hzc, hzb⟩

private theorem hsumFund :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (S : Finset GaussianInt), ∀ (R : Finset GaussianInt),
            (LatticeFundamentalSet (TilingLattice C) S) → ((LatticeFundamentalSet (TilingLattice
            C) R) → (∀ (f : GaussianInt → ℝ), (∀ x, ∀ v, v ∈ TilingLattice C → f (x + v) = f x) →
            ((∑ x ∈ S, f x) = ∑ x ∈ R, f x))) ) := by
  classical
  intro C S R hS hR' f hper
  apply Finset.sum_bij (fun a _ => Classical.choose (hR' a))
  · intro a ha
    exact (Classical.choose_spec (hR' a)).1.1
  · intro a ha a' ha' heq
    have hfa := (Classical.choose_spec (hR' a)).1.2
    have hfa' := (Classical.choose_spec (hR' a')).1.2
    have hfa'' : a' - Classical.choose (hR' a) ∈ TilingLattice C := by
      convert hfa' using 1
      rw [heq]
    have hd : a - a' ∈ TilingLattice C := by
      have hs := (TilingLattice C).add_mem hfa
        ((TilingLattice C).neg_mem hfa'')
      convert hs using 1; abel
    have hchoose : Classical.choose (hS a) = a := by
      exact ((Classical.choose_spec (hS a)).2 a ⟨ha, by simp⟩).symm
    have hchoose' : a' = Classical.choose (hS a) :=
      (Classical.choose_spec (hS a)).2 a' ⟨ha', hd⟩
    rw [hchoose] at hchoose'
    exact hchoose'.symm
  · intro b hb
    obtain ⟨a, ⟨ha, hba⟩, _⟩ := hS b
    have haR : a - Classical.choose (hR' a) ∈ TilingLattice C :=
      (Classical.choose_spec (hR' a)).1.2
    have hbRep : b - Classical.choose (hR' a) ∈ TilingLattice C := by
      have hsum := (TilingLattice C).add_mem hba haR
      convert hsum using 1; abel
    have hchoose : Classical.choose (hR' a) =
        Classical.choose (hR' b) :=
      (Classical.choose_spec (hR' b)).2 _
        ⟨(Classical.choose_spec (hR' a)).1.1, hbRep⟩
    have hbchoose : Classical.choose (hR' b) = b :=
      ((Classical.choose_spec (hR' b)).2 b ⟨hb, by simp⟩).symm
    exact ⟨a, ha, hchoose.trans hbchoose⟩
  · intro a ha
    let r := Classical.choose (hR' a)
    have hv : a - r ∈ TilingLattice C := by
      exact (Classical.choose_spec (hR' a)).1.2
    have hp := hper r (a - r) hv
    calc
      f a = f (r + (a - r)) := by congr 1; abel
      _ = f r := hp

private theorem hfundTranslate :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (LatticeFundamentalSet (TilingLattice C) T.cells)
            → (∀ (s : GaussianInt), LatticeFundamentalSet (TilingLattice C) (T.cells.image (fun x
            => x + s))) ) := by
  classical
  intro C T hfund s x
  obtain ⟨r, ⟨hr, hxr⟩, huniq⟩ := hfund (x - s)
  refine ⟨r + s, ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩, ?_⟩
  · convert hxr using 1; abel
  · intro y hy
    rcases Finset.mem_image.mp hy.1 with ⟨r', hr', rfl⟩
    have hxr' : (x - s) - r' ∈ TilingLattice C := by
      convert hy.2 using 1; abel
    have heq := huniq r' ⟨hr', hxr'⟩
    simpa using congrArg (fun z => z + s) heq

private theorem hsumTranslate :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (LatticeFundamentalSet (TilingLattice C) T.cells)
            → ((∀ (S : Finset GaussianInt), ∀ (R : Finset GaussianInt), (LatticeFundamentalSet
            (TilingLattice C) S) → ((LatticeFundamentalSet (TilingLattice C) R) → (∀ (f :
            GaussianInt → ℝ), (∀ x, ∀ v, v ∈ TilingLattice C → f (x + v) = f x) → ((∑ x ∈ S, f x)
            = ∑ x ∈ R, f x)))) → ((∀ (s : GaussianInt), LatticeFundamentalSet (TilingLattice C)
            (T.cells.image (fun x => x + s))) → (∀ (s : GaussianInt), ∀ (f : GaussianInt → ℝ), (∀
            x, ∀ v, v ∈ TilingLattice C → f (x + v) = f x) → ((∑ x ∈ T.cells, f (x + s)) = ∑ x ∈
            T.cells, f x)))) ) := by
  classical
  intro C T hfund hsumFund hfundTranslate s f hper
  have hinj : Function.Injective (fun x : GaussianInt => x + s) := by
    intro x y hxy
    exact add_right_cancel hxy
  have himage : (∑ y ∈ T.cells.image (fun x => x + s), f y) =
      ∑ x ∈ T.cells, f (x + s) :=
    Finset.sum_image (fun a ha b hb hab => hinj hab)
  calc
    _ = ∑ y ∈ T.cells.image (fun x => x + s), f y := himage.symm
    _ = ∑ x ∈ T.cells, f x :=
      (hsumFund T.cells (T.cells.image (fun x => x + s)) hfund
        (hfundTranslate s) f hper).symm

private theorem hFstencil_sum :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (g : IntegerLatticeFunction),
        (∀ (s : GaussianInt), ∀ (f : GaussianInt → ℝ), (∀ x, ∀ v, v ∈ TilingLattice C → f (x + v)
            = f x) → ((∑ x ∈ T.cells, f (x + s)) = ∑ x ∈ T.cells, f x)) → (∀ (b : ℝ × ℝ),
        let F : GaussianInt → ℝ := fun x => (g x : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re + b.2 * x.im)
        (∀ (x : GaussianInt), ∀ (v : GaussianInt), (v ∈ TilingLattice C) → (F (x + v) = F x)) →
            ((∑ x ∈ T.cells, RealFourNeighborLaplacian F x) = 0)) ) := by
  classical
  intro C T g hsumTranslate b F hFperiod
  let I : GaussianInt := ⟨0, 1⟩
  have hs1 := hsumTranslate (1 : GaussianInt) F hFperiod
  have hsm1 := hsumTranslate (-1 : GaussianInt) F hFperiod
  have hsI := hsumTranslate I F hFperiod
  have hsmI := hsumTranslate (-I) F hFperiod
  have hsm1' : (∑ x ∈ T.cells, F (x - 1)) = ∑ x ∈ T.cells, F x := by
    convert hsm1 using 1
  have hsmI' : (∑ x ∈ T.cells, F (x - I)) = ∑ x ∈ T.cells, F x := by
    convert hsmI using 1
  simp only [RealFourNeighborLaplacian, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [hs1, hsm1', hsI, hsmI']
  rw [← Finset.mul_sum]
  ring


private theorem hF_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ),
        let F : GaussianInt → ℝ := fun x => (g x : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re + b.2 * x.im)
        let u : GaussianInt → ℝ := fun x => (g x : ℝ)
        let vfun : GaussianInt → ℝ := fun x =>
          LatticeQuadraticForm (CircleMatrix C) x +
            dotProduct ![b.1, b.2] ![(x.re : ℝ), (x.im : ℝ)]
        F = fun x => u x - vfun x ) := by
  classical
  intro C g b F u vfun
  funext x
  simp [F, u, vfun, dotProduct]
  ring

private theorem hFlap :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ),
        let F : GaussianInt → ℝ := fun x => (g x : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re + b.2 * x.im)
        let u : GaussianInt → ℝ := fun x => (g x : ℝ)
        let vfun : GaussianInt → ℝ := fun x =>
          LatticeQuadraticForm (CircleMatrix C) x +
            dotProduct ![b.1, b.2] ![(x.re : ℝ), (x.im : ℝ)]
        ((CircleMatrix C).IsSymm) → ((F = fun x => u x - vfun x) → (∀ (x : GaussianInt),
            RealFourNeighborLaplacian F x = (FourNeighborLaplacian g x : ℝ) - Matrix.trace
            (CircleMatrix C))) ) := by
  classical
  intro C g b F u vfun hsym hF_eq x
  rw [hF_eq]
  have hlin := RealLaplacianLinearity u vfun 1 (-1) x
  have hquad := QuadraticAffineLaplacian (CircleMatrix C) hsym
    ![b.1, b.2] 0 x
  have hquad' : RealFourNeighborLaplacian vfun x =
      Matrix.trace (CircleMatrix C) := by
    simpa [vfun] using hquad
  rw [show (fun y => u y - vfun y) =
    (fun y => (1 : ℝ) * u y + (-1 : ℝ) * vfun y) by
      funext y
      ring]
  rw [hlin]
  simp only [one_mul, neg_one_mul]
  rw [IntegerLaplacianCastBridge, hquad']
  ring

private theorem hsumDelta :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (g : IntegerLatticeFunction), ∀ (b : ℝ × ℝ),
        let F : GaussianInt → ℝ := fun x => (g x : ℝ) -
          LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re + b.2 * x.im)
        ((∑ x ∈ T.cells, RealFourNeighborLaplacian F x) = 0) → ((∀ (x : GaussianInt),
            RealFourNeighborLaplacian F x = (FourNeighborLaplacian g x : ℝ) - Matrix.trace
            (CircleMatrix C)) → ((∑ x ∈ T.cells, (FourNeighborLaplacian g x : ℝ)) = (T.cells.card
            : ℝ) * Matrix.trace (CircleMatrix C))) ) := by
  classical
  intro C T g b F hFstencil_sum hFlap
  calc
    _ = ∑ x ∈ T.cells,
        (RealFourNeighborLaplacian F x + Matrix.trace (CircleMatrix C)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hFlap]
          ring
    _ = _ := by rw [Finset.sum_add_distrib, hFstencil_sum]; simp

private theorem htrace :
    (by
      classical
      exact
        ∀ (C : BandCircle), Matrix.trace (CircleMatrix C) = 1 / (C.1.1.1 : ℝ) ) := by
  classical
  intro C
  simp [CircleMatrix, BandCircleEuclideanData, Matrix.trace, Matrix.diag]
  ring

private theorem hcurvCast :
    (by
      classical
      exact
        ∀ (C : BandCircle), (C.1.1.1.natAbs : ℝ) = (C.1.1.1 : ℝ) ) := by
  classical
  intro C
  have hi : (C.1.1.1.natAbs : ℤ) = C.1.1.1 :=
    Int.natAbs_of_nonneg (le_of_lt C.2)
  have hcast : ((C.1.1.1.natAbs : ℤ) : ℝ) =
      (C.1.1.1.natAbs : ℝ) := Int.cast_natCast _
  calc
    (C.1.1.1.natAbs : ℝ) = ((C.1.1.1.natAbs : ℤ) : ℝ) := hcast.symm
    _ = (C.1.1.1 : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hi

private theorem hsumDelta_one :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (g : IntegerLatticeFunction), (T.cells.card =
            C.1.1.1.natAbs) → (((∑ x ∈ T.cells, (FourNeighborLaplacian g x : ℝ)) = (T.cells.card
            : ℝ) * Matrix.trace (CircleMatrix C)) → ((Matrix.trace (CircleMatrix C) = 1 /
            (C.1.1.1 : ℝ)) → (((C.1.1.1.natAbs : ℝ) = (C.1.1.1 : ℝ)) → ((∑ x ∈ T.cells,
            (FourNeighborLaplacian g x : ℝ)) = 1)))) ) := by
  classical
  intro C T g hcell_curv hsumDelta htrace hcurvCast
  rw [hsumDelta, htrace]
  have hcardReal : (T.cells.card : ℝ) = (C.1.1.1.natAbs : ℝ) := by
    exact_mod_cast hcell_curv
  rw [hcardReal, hcurvCast]
  have hcne : (C.1.1.1 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt C.2)
  field_simp

private theorem hDfilterProp :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        (∀ (z : GaussianInt), z ∈ D ↔ z ∈ T.cells ∧ z ∉ BoundaryFootprintVertices T) → (D =
            T.cells.filter (fun x => x ∉ BoundaryFootprintVertices T)) ) := by
  classical
  intro T h D hDcells
  ext z
  simp only [Finset.mem_filter]
  exact hDcells z

private theorem hcell_partition :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        (D = T.cells.filter (fun x => x ∉ BoundaryFootprintVertices T)) → (
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        D.card + B.card = T.cells.card) ) := by
  classical
  intro T h D hDfilterProp B
  rw [hDfilterProp]
  dsimp [B]
  have h := Finset.card_filter_add_card_filter_not
    (s := T.cells) (fun x => x ∉ BoundaryFootprintVertices T)
  simpa only [not_not] using h

private theorem hsum_partition :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        (D = T.cells.filter (fun x => x ∉ BoundaryFootprintVertices T)) → (
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        ∀ (f : GaussianInt → ℝ), (∑ x ∈ D, f x) + (∑ x ∈ B, f x) = ∑ x ∈ T.cells, f x) ) := by
  classical
  intro T h D hDfilterProp B f
  rw [hDfilterProp]
  dsimp [B]
  simpa only [not_not] using
    Finset.sum_filter_add_sum_filter_not T.cells
      (fun x => x ∉ BoundaryFootprintVertices T) f

private theorem hB_lap :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : IntegerLatticeFunction), (∀ x ∈ BoundaryFootprintVertices T,
            FourNeighborLaplacian g x = (1 : ℤ)) → (
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        (∑ x ∈ B, (FourNeighborLaplacian g x : ℝ)) = B.card) ) := by
  classical
  intro T g hweb B
  calc
    _ = ∑ x ∈ B, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' : x ∈ BoundaryFootprintVertices T := by
        simp only [Finset.mem_filter, B] at hx
        exact hx.2
      rw [hweb x hx']
      norm_num
    _ = B.card := by simp [B]

private theorem hD_lap_real :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g : IntegerLatticeFunction),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        ((∑ x ∈ T.cells, (FourNeighborLaplacian g x : ℝ)) = 1) → (
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        (∀ (f : GaussianInt → ℝ), (∑ x ∈ D, f x) + (∑ x ∈ B, f x) = ∑ x ∈ T.cells, f x) → (((∑ x
            ∈ B, (FourNeighborLaplacian g x : ℝ)) = B.card) → ((∑ x ∈ D, (FourNeighborLaplacian g
            x : ℝ)) = 1 - (B.card : ℝ)))) ) := by
  classical
  intro T h g D hsumDelta_one B hsum_partition hB_lap
  have hs := hsum_partition (fun x => (FourNeighborLaplacian g x : ℝ))
  rw [hB_lap] at hs
  linarith

private theorem hD_lap_int :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g : IntegerLatticeFunction),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        ((∑ x ∈ D, (FourNeighborLaplacian g x : ℝ)) = 1 - (B.card : ℝ)) → ((∑ x ∈ D,
            FourNeighborLaplacian g x) = 1 - (B.card : ℤ)) ) := by
  classical
  intro T h g D B hD_lap_real
  exact_mod_cast hD_lap_real

private theorem hsum_sigma :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g : IntegerLatticeFunction),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        let B : Finset GaussianInt := T.cells.filter
          (fun x => x ∈ BoundaryFootprintVertices T)
        ((∑ x ∈ D, FourNeighborLaplacian g x) = 1 - (B.card : ℤ)) → ((∑ x ∈ D, (2 +
            FourNeighborLaplacian g x)) = (2 * D.card : ℤ) + 1 - B.card) ) := by
  classical
  intro T h g D B hD_lap_int
  rw [Finset.sum_add_distrib, hD_lap_int]
  simp only [Finset.sum_const,
    nsmul_eq_mul]
  ring

private theorem hpairfilter :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
        let D : Finset GaussianInt := h.domain.filter
          (fun x => @decide (x ∉ BoundaryFootprintVertices T)
            (Classical.propDecidable _))
        ((D.product D).filter fun (e : GaussianInt × GaussianInt) => @decide
            (FourNeighborAdjacent e.1 e.2) (Classical.propDecidable _)) = ((D.product D).filter
            fun e => FourNeighborAdjacent e.1 e.2) ) := by
  classical
  intro T h D
  ext e
  simp only [Finset.mem_filter]
  have hdec : @decide (FourNeighborAdjacent e.1 e.2)
      (Classical.propDecidable _) = true ↔ FourNeighborAdjacent e.1 e.2 := by
    cases Classical.propDecidable _ <;> simp
  rw [hdec]

private theorem hhalf :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          ∀ (h : PartialOdometer),
            let D : Finset GaussianInt :=
              h.domain.filter fun x =>
                @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _);
            2 *
                  ((D.filter fun z => z + 1 ∈ D).card +
                    (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card) /
                2 =
              (D.filter fun z => z + 1 ∈ D).card +
                (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card
    ) := by
  classical
  intro T h D
  omega

end PeriodicIndegreeGeometry

namespace PeriodicCountBridge

private theorem hcountBridge :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), (BandPrototile C.1.1 T) → ((LatticeTile T) → (∀ (D
            : Finset GaussianInt), (∀ z, z ∈ D ↔ z ∈ FootprintVertices T ∧ z ∉
            BoundaryFootprintVertices T) → ((∀ z, z ∈ FootprintVertices T → z ∉
            BoundaryFootprintVertices T →
            z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - (⟨0, 1⟩ : GaussianInt) ∈ T.cells ∧
              z - 1 - (⟨0, 1⟩ : GaussianInt) ∈ T.cells) → ((3 * (D.card : Int) - T.cells.card +
                  1) = (D.filter fun z => z + 1 ∈ D).card + (D.filter fun z => z + (⟨0, 1⟩ :
                  GaussianInt) ∈ D).card)))) ) := by
  classical
  intro C T hT hlat D hDmem hsectorAll
  have htiles := LatticeTileGridStructure T hlat
  have hcells : T.cells.Nonempty := htiles.1.1
  have heuler := LatticeTileGridEulerCount T hlat
  have hreg := LatticeEdgeRegularity C T hT hlat
  let I : GaussianInt := ⟨0, 1⟩
  let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
    ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
  let N : Nat → Nat := fun k =>
    (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
  have hinc := FiniteSquareIncidenceIdentities T hcells htiles.2.1
  change 4 * T.cells.card = N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4 ∧
    (FootprintVertices T).ncard = N 1 + N 2 + N 3 + N 4 ∧
    2 * (FootprintEdges T).ncard = 4 * T.cells.card +
      (BoundaryFootprintEdges T).ncard ∧
    (BoundaryFootprintEdges T).ncard = N 1 + N 2 + N 3 at hinc
  have hvertex_partition : (FootprintVertices T).ncard =
      D.card + (BoundaryFootprintEdges T).ncard  := PeriodicIndegreeGeometry.hvertex_partition T
          D hinc
      (PeriodicIndegreeGeometry.hN4 T D hDmem hsectorAll hcells
      (TileCornerMultiplicity.cornerCount T) (PeriodicIndegreeGeometry.hfull_not_boundary T
      hcells))
  -- A base point and direction give a unique tag for each footprint edge.
  let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
    if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
  have edgeOf_injective := LatticeCellEdges.edge_encoding_injective
  let V := cornerBag.toFinset
  have hEV := BoundaryFootprintInclusion.edgeVertex T
  let E := (V.product (Finset.univ : Finset Bool)).filter
    fun e => edgeOf e ∈ FootprintEdges T
  have hEmem := PeriodicIndegreeGeometry.hEmem T (PeriodicIndegreeGeometry.hV T hcells) hEV
  have hEset := PeriodicIndegreeGeometry.hEset T hEmem
  have hEcard : E.card = (FootprintEdges T).ncard  := PeriodicIndegreeGeometry.hEcard T
      edgeOf_injective hEset
  let BE := E.filter fun e => edgeOf e ∈ BoundaryFootprintEdges T
  have hBEcard : BE.card = (BoundaryFootprintEdges T).ncard  := PeriodicIndegreeGeometry.hBEcard
      T edgeOf_injective
      (PeriodicIndegreeGeometry.hBEset T hEset (PeriodicIndegreeGeometry.hBEsub T))
  let A := E.filter fun e => edgeOf e ∉ BoundaryFootprintEdges T
  have hApart : A.card + BE.card = E.card  := PeriodicIndegreeGeometry.hApart T
  have hEocc := PeriodicIndegreeGeometry.hEocc T edgeOf_injective hEmem
  -- A shared side has an open rectangle inside its two incident squares.
  let step : Bool → GaussianInt := fun b => if b then I else 1
  have hedgeOf := PeriodicIndegreeGeometry.hedgeOf
  have hDedge_nonboundary := PeriodicIndegreeGeometry.hDedge_nonboundary T D hDmem hcells
  -- Swap the vertex and edge sums to count the same incidences twice.
  let J := A.filter fun q => q.1 ∈ D ∧ q.1 + step q.2 ∈ D
  have hdegree_count : A.card + J.card = 4 * D.card  := PeriodicIndegreeGeometry.hdegree_count T D
      (PeriodicIndegreeGeometry.hAendpoint T D hDmem hreg hEV hEmem
      (PeriodicIndegreeGeometry.hshared T hinc hEocc
      (PeriodicIndegreeGeometry.hBEocc T edgeOf_injective))
      (PeriodicIndegreeGeometry.hhorizontal T) (PeriodicIndegreeGeometry.hvertical T) hedgeOf)
      (PeriodicIndegreeGeometry.hdegree_sum T D (PeriodicIndegreeGeometry.hdegree T D hDmem
      hsectorAll hEocc hDedge_nonboundary) (PeriodicIndegreeGeometry.hendSum D hedgeOf))
  let east := D.filter fun z => z + 1 ∈ D
  let north := D.filter fun z => z + I ∈ D
  have hJcard : J.card = east.card + north.card  := PeriodicIndegreeGeometry.hJcard T D
      (PeriodicIndegreeGeometry.hJset T D
      (PeriodicIndegreeGeometry.hJmem T D hDmem hreg hEmem hedgeOf hDedge_nonboundary))
      (PeriodicIndegreeGeometry.hdisj D)
  change (3 * (D.card : Int) - T.cells.card + 1) = east.card + north.card
  omega

end PeriodicCountBridge

theorem PeriodicTileTotalIndegree (C : BandCircle)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hT : BandPrototile C.1.1 T) (hlat : LatticeTile T)
    (htile : ExactTileTiling (RegularTileFamily T (TilingLattice C)))
    (hweb : ∀ x, x ∈ BoundaryFootprintVertices T →
      FourNeighborLaplacian g x = 1)
    (hperiod : ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
      (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
          (b.1 * (x + v).re + b.2 * (x + v).im) =
        (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im)) :
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    (∑ x ∈ D, (2 + FourNeighborLaplacian g x)) =
      ((((D.product D).filter fun (e : GaussianInt × GaussianInt) =>
        @decide (FourNeighborAdjacent e.1 e.2)
          (Classical.propDecidable _)).card / 2 : ℕ) : ℤ) := by
-- BODY
  classical
  -- East and north representatives count each unoriented induced edge once.
  have hordered (D : Finset GaussianInt) :
      ((D.product D).filter fun (e : GaussianInt × GaussianInt) =>
        FourNeighborAdjacent e.1 e.2).card =
      2 * ((D.filter fun z => z + 1 ∈ D).card +
        (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card) :=
            PeriodicIndegreeGeometry.hordered D
  -- Disk Euler count and the four interior incidences give 3m - c + 1.
  have hcountBridge (D : Finset GaussianInt)
      (hDmem : ∀ z, z ∈ D ↔ z ∈ FootprintVertices T ∧ z ∉ BoundaryFootprintVertices T)
      (hsectorAll : ∀ z, z ∈ FootprintVertices T → z ∉ BoundaryFootprintVertices T →
        z ∈ T.cells ∧ z - 1 ∈ T.cells ∧ z - (⟨0, 1⟩ : GaussianInt) ∈ T.cells ∧
          z - 1 - (⟨0, 1⟩ : GaussianInt) ∈ T.cells) :
      (3 * (D.card : Int) - T.cells.card + 1) =
        (D.filter fun z => z + 1 ∈ D).card +
        (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card :=
            PeriodicCountBridge.hcountBridge C T hT hlat D hDmem hsectorAll
  have htiles := LatticeTileGridStructure T hlat
  have heuler := LatticeTileGridEulerCount T hlat
  let D : Finset GaussianInt := h.domain.filter
    (fun x => @decide (x ∉ BoundaryFootprintVertices T)
      (Classical.propDecidable _))
  change (∑ x ∈ D, (2 + FourNeighborLaplacian g x)) =
    ((((D.product D).filter fun (e : GaussianInt × GaussianInt) =>
      @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)
  have hcells : T.cells.Nonempty := htiles.1.1
  rcases htiles.2.2 with ⟨p, x₀, x₁, hpnd, hplen, hhead, hlast,
    hverts, hclose, hadj, hedges⟩
  have hDmem := PeriodicIndegreeGeometry.hDmem T h hdom
  -- Exact tiling makes the cell bases a finite set of residue representatives.
  have hcell_cover := PeriodicIndegreeGeometry.hcell_cover C T htile
  have hcell_residue_unique := PeriodicIndegreeGeometry.hcell_residue_unique C T h g hdom
      htile hweb heuler p x₀ x₁ hverts hedges
      (PeriodicIndegreeGeometry.hboundary_card T p hpnd hverts)
      (PeriodicIndegreeGeometry.htranslation_rigid T hcells) hcell_cover
  have hfund := PeriodicIndegreeGeometry.hfund C T hcell_cover hcell_residue_unique
  obtain ⟨R, hR, hRcard⟩ := TilingLatticeIndex C
  have hcell_curv : T.cells.card = C.1.1.1.natAbs  := PeriodicIndegreeGeometry.hcell_curv C T R
      hRcard
      (PeriodicIndegreeGeometry.hcell_card C T hcell_residue_unique hfund R hR)
  have hsectorAll := PeriodicIndegreeGeometry.hsectorAll T (PeriodicIndegreeGeometry.hstatusRight
      T hcells) (PeriodicIndegreeGeometry.hstatusDown T hcells)
      (PeriodicIndegreeGeometry.hstatusLeft T hcells) (PeriodicIndegreeGeometry.hsomeSector T
      hcells)
  have hDcells := PeriodicIndegreeGeometry.hDcells T h hDmem hsectorAll
      (PeriodicIndegreeGeometry.hcellBaseFV T hcells)
  have hsumTranslate := PeriodicIndegreeGeometry.hsumTranslate C T hfund
      (PeriodicIndegreeGeometry.hsumFund C) (PeriodicIndegreeGeometry.hfundTranslate C T hfund)
  -- Each translated periodic stencil has the same sum over the representatives.
  rcases hperiod with ⟨b, hb⟩
  let F : GaussianInt → ℝ := fun x => (g x : ℝ) -
    LatticeQuadraticForm (CircleMatrix C) x - (b.1 * x.re + b.2 * x.im)
  have hFperiod (x v : GaussianInt) (hv : v ∈ TilingLattice C) :
      F (x + v) = F x := hb v hv x
  have hDfilterProp := PeriodicIndegreeGeometry.hDfilterProp T h hDcells
  let B : Finset GaussianInt := T.cells.filter
    (fun x => x ∈ BoundaryFootprintVertices T)
  have hcell_partition : D.card + B.card = T.cells.card  :=
      PeriodicIndegreeGeometry.hcell_partition T h hDfilterProp
  have hsum_sigma :
      (∑ x ∈ D, (2 + FourNeighborLaplacian g x)) =
        (2 * D.card : ℤ) + 1 - B.card := PeriodicIndegreeGeometry.hsum_sigma T h g
            (PeriodicIndegreeGeometry.hD_lap_int T h g (PeriodicIndegreeGeometry.hD_lap_real T h
            g (PeriodicIndegreeGeometry.hsumDelta_one C T g hcell_curv
            (PeriodicIndegreeGeometry.hsumDelta C T g b (PeriodicIndegreeGeometry.hFstencil_sum C
            T g hsumTranslate b hFperiod) (PeriodicIndegreeGeometry.hFlap C g b
            (CircleMatrixSymmetry.symmetric C) (PeriodicIndegreeGeometry.hF_eq C g b)))
            (PeriodicIndegreeGeometry.htrace C) (PeriodicIndegreeGeometry.hcurvCast C))
            (PeriodicIndegreeGeometry.hsum_partition T h hDfilterProp)
            (PeriodicIndegreeGeometry.hB_lap T g hweb)))
  rw [hsum_sigma]
  have hc := hcountBridge D hDmem hsectorAll
  have hpairfilter : ((D.product D).filter fun (e : GaussianInt × GaussianInt) =>
      @decide (FourNeighborAdjacent e.1 e.2) (Classical.propDecidable _)) =
      ((D.product D).filter fun e => FourNeighborAdjacent e.1 e.2) :=
          PeriodicIndegreeGeometry.hpairfilter T h
  rw [hpairfilter, hordered]
  have hhalf :
      (2 * ((D.filter fun z => z + 1 ∈ D).card +
        (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card)) / 2 =
      (D.filter fun z => z + 1 ∈ D).card +
        (D.filter fun z => z + (⟨0, 1⟩ : GaussianInt) ∈ D).card :=
            PeriodicIndegreeGeometry.hhalf T h
  rw [hhalf]
  omega

end ApollonianSuperharmonic

end
