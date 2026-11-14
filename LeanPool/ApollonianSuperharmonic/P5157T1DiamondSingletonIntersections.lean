/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows

-- [TABLET NODE: P5157T1DiamondSingletonIntersections]

/-!
# P5157T1DiamondSingletonIntersections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondSingletonGeometry

private theorem translateMem (T : ProtoTile) (u z : GaussianInt) :
      z ∈ (TileTranslation T u).cells ↔ z - u ∈ T.cells := by
  classical
  rw [(TileTranslationFormulas T u).1]
  simp only [Finset.mem_image, GaussianTranslation]
  constructor
  · rintro ⟨w, hw, he⟩
    have hwz : w = z - u := (eq_sub_iff_add_eq).mpr he
    simpa only [← hwz] using hw
  · intro hz
    exact ⟨z - u, hz, sub_add_cancel z u⟩

private theorem bounds (T : ProtoTile) (hne : T.cells.Nonempty) (lo hi : GaussianInt)
      (hcells : ∀ w ∈ T.cells,
        lo.re ≤ w.re ∧ w.re ≤ hi.re ∧ lo.im ≤ w.im ∧ w.im ≤ hi.im)
      (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices T) :
      lo.re ≤ v.re ∧ v.re ≤ hi.re + 1 ∧ lo.im ≤ v.im ∧ v.im ≤ hi.im + 1 := by
  classical
  rw [BoundaryFootprintVertices, ite_eq_left hne] at hv
  obtain ⟨e, ⟨w, he⟩, hv⟩ := hv
  rcases he with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hw with ⟨hw, _⟩ | ⟨_, hw⟩ <;>
      have hb := hcells _ hw <;>
      rcases hv with rfl | rfl <;>
      (try simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
        Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one] at hb ⊢) <;> omega

private theorem unitBounds (c v : GaussianInt)
      (hv : v ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile)) :
      c.re ≤ v.re ∧ v.re ≤ c.re + 1 ∧ c.im ≤ v.im ∧ v.im ≤ c.im + 1 := by
  classical
  have bounds (T : ProtoTile) (hne : T.cells.Nonempty) (lo hi : GaussianInt)
      (hcells : ∀ w ∈ T.cells,
        lo.re ≤ w.re ∧ w.re ≤ hi.re ∧ lo.im ≤ w.im ∧ w.im ≤ hi.im)
      (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices T) :
      lo.re ≤ v.re ∧ v.re ≤ hi.re + 1 ∧ lo.im ≤ v.im ∧ v.im ≤ hi.im + 1 := bounds T hne lo hi
          hcells v hv
  apply bounds _ (Finset.singleton_nonempty _) c c _ v hv
  intro w hw
  simpa only [Finset.mem_singleton.mp hw] using
    (show c.re ≤ c.re ∧ c.re ≤ c.re ∧ c.im ≤ c.im ∧ c.im ≤ c.im from
      ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)

end DiamondSingletonGeometry

theorem P5157T1DiamondSingletonIntersections (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
    let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
    let a : GaussianInt := ⟨-(k : Int) - 1, (k : Int) - 1⟩
    let b : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
    let A : ProtoTile := ⟨{a}, a⟩
    let B : ProtoTile := ⟨{b}, b⟩
    (Disjoint D.cells A.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices A = {a + 1, a + 1 + ⟨0, 1⟩} ∧
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges A = {{a + 1, a + 1 + ⟨0, 1⟩}}) ∧
    (Disjoint Eminus.cells A.cells ∧
      BoundaryFootprintVertices Eminus ∩ BoundaryFootprintVertices A = {a, a + 1} ∧
      BoundaryFootprintEdges Eminus ∩ BoundaryFootprintEdges A = {{a, a + 1}}) ∧
    (Disjoint D.cells B.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B = {b, b + ⟨0, 1⟩} ∧
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges B = {{b, b + ⟨0, 1⟩}}) ∧
    (Disjoint Eplus.cells B.cells ∧
      BoundaryFootprintVertices Eplus ∩ BoundaryFootprintVertices B = {b, b + 1} ∧
      BoundaryFootprintEdges Eplus ∩ BoundaryFootprintEdges B = {{b, b + 1}}) := by
-- BODY
  classical
  dsimp only
  let D := DiamondTile k
  let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
  let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
  let a : GaussianInt := ⟨-(k : Int) - 1, (k : Int) - 1⟩
  let b : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
  have translateMem (T : ProtoTile) (u z : GaussianInt) :
      z ∈ (TileTranslation T u).cells ↔ z - u ∈ T.cells := DiamondSingletonGeometry.translateMem
          T u z
  have dcell (z : GaussianInt) := (P4194T1DiamondCellRows k z).1
  have ecell (z : GaussianInt) := (P4194T1DiamondCellRows (k - 1) z).1
  have da : a ∉ D.cells := by
    change a ∉ DiamondCellDomain k
    rw [dcell]
    simp only [a]
    omega
  have db : b ∉ D.cells := by
    change b ∉ DiamondCellDomain k
    rw [dcell]
    simp only [b]
    omega
  have dma : a ∉ Eminus.cells := by
    rw [translateMem]
    change a - ⟨-(k : Int), 1 - (k : Int)⟩ ∉ DiamondCellDomain (k - 1)
    rw [ecell]
    simp [a]
    omega
  have dpb : b ∉ Eplus.cells := by
    rw [translateMem]
    change b - ⟨(k : Int), 1 - (k : Int)⟩ ∉ DiamondCellDomain (k - 1)
    rw [ecell]
    simp [b]
    omega
  have dleft : a + 1 ∈ D.cells := by
    change a + 1 ∈ DiamondCellDomain k
    rw [dcell]
    simp [a]
    omega
  have dright : b - 1 ∈ D.cells := by
    change b - 1 ∈ DiamondCellDomain k
    rw [dcell]
    simp [b]
    omega
  have emtop : a - ⟨0, 1⟩ ∈ Eminus.cells := by
    rw [translateMem]
    change a - ⟨0, 1⟩ - ⟨-(k : Int), 1 - (k : Int)⟩ ∈ DiamondCellDomain (k - 1)
    rw [ecell]
    simp [a]
    omega
  have eptop : b - ⟨0, 1⟩ ∈ Eplus.cells := by
    rw [translateMem]
    change b - ⟨0, 1⟩ - ⟨(k : Int), 1 - (k : Int)⟩ ∈ DiamondCellDomain (k - 1)
    rw [ecell]
    simp [b]
    omega
  have bounds (T : ProtoTile) (hne : T.cells.Nonempty) (lo hi : GaussianInt)
      (hcells : ∀ w ∈ T.cells,
        lo.re ≤ w.re ∧ w.re ≤ hi.re ∧ lo.im ≤ w.im ∧ w.im ≤ hi.im)
      (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices T) :
      lo.re ≤ v.re ∧ v.re ≤ hi.re + 1 ∧ lo.im ≤ v.im ∧ v.im ≤ hi.im + 1 :=
          DiamondSingletonGeometry.bounds T hne lo hi hcells v hv
  have unitBounds (c v : GaussianInt)
      (hv : v ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile)) :
      c.re ≤ v.re ∧ v.re ≤ c.re + 1 ∧ c.im ≤ v.im ∧ v.im ≤ c.im + 1 :=
          DiamondSingletonGeometry.unitBounds c v hv
  have dBounds (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices D) :
      -(k : Int) ≤ v.re ∧ v.re ≤ (k : Int) := by
    have hb := bounds D ⟨_, dleft⟩ ⟨-(k : Int), 0⟩
      ⟨(k : Int) - 1, 2 * (k : Int) - 1⟩ (by
        intro w hw
        have hh := (dcell w).mp hw
        dsimp
        omega) v hv
    exact ⟨hb.1, by simpa using hb.2.1⟩
  have eBounds (u : GaussianInt) (hu : u.im = 1 - (k : Int)) (v : GaussianInt)
      (hv : v ∈ BoundaryFootprintVertices (TileTranslation (DiamondTile (k - 1)) u)) :
      v.im ≤ (k : Int) - 1 := by
    have ht : (TileTranslation (DiamondTile (k - 1)) u).cells.Nonempty := by
      refine ⟨u, (translateMem _ _ _).mpr ?_⟩
      change u - u ∈ DiamondCellDomain (k - 1)
      rw [sub_self, ecell]
      norm_num
      omega
    have hb := bounds _ ht ⟨u.re - 2 * (k : Int), 1 - (k : Int)⟩
      ⟨u.re + 2 * (k : Int), (k : Int) - 2⟩ (by
        intro w hw
        have hh := (ecell (w - u)).mp ((translateMem _ _ _).mp hw)
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, hu] at hh
        dsimp
        omega) v hv
    have hh := hb.2.2.2
    dsimp at hh
    omega
  have finish (T : ProtoTile) (c x y : GaussianInt) (hc : c ∉ T.cells)
      (hxy : x ≠ y) (hT : {x, y} ∈ BoundaryFootprintEdges T)
      (hU : {x, y} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile))
      (hsub : ∀ v, v ∈ BoundaryFootprintVertices T →
        v ∈ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) → v = x ∨ v = y) :
      Disjoint T.cells (⟨{c}, c⟩ : ProtoTile).cells ∧
      BoundaryFootprintVertices T ∩ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) = {x, y} ∧
      BoundaryFootprintEdges T ∩ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) = {{x, y}} := by
    have hne : T.cells.Nonempty := by
      obtain ⟨w, ⟨_, hw⟩ | ⟨_, hw⟩⟩ := hT
      all_goals rcases hw with ⟨hw, _⟩ | ⟨_, hw⟩ <;> exact ⟨_, hw⟩
    have endpoint (U : ProtoTile) (hU : U.cells.Nonempty) (e : Finset GaussianInt)
        (he : e ∈ BoundaryFootprintEdges U) (v : GaussianInt) (hv : v ∈ e) :
        v ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hU]
      exact ⟨e, he, hv⟩
    have hvertices : BoundaryFootprintVertices T ∩
        BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) = {x, y} := by
      ext v
      constructor
      · intro hv
        exact hsub v hv.1 hv.2
      · intro hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        have hve : v ∈ ({x, y} : Finset GaussianInt) := by simpa using hv
        exact ⟨endpoint T hne _ hT v hve,
          endpoint _ (Finset.singleton_nonempty c) _ hU v hve⟩
    refine ⟨Finset.disjoint_singleton_right.mpr hc, hvertices, ?_⟩
    ext e
    constructor
    · intro he
      have hcard : e.card = 2 := by
        obtain ⟨w, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := he.1
        all_goals simp [Zsqrtd.ext_iff]
      have hsubset : e ⊆ {x, y} := by
        intro v hv
        have hv' : v ∈ BoundaryFootprintVertices T ∩
            BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) :=
          ⟨endpoint T hne e he.1 v hv,
            endpoint _ (Finset.singleton_nonempty c) e he.2 v hv⟩
        rw [hvertices] at hv'
        simpa using hv'
      have heq : e = {x, y} := Finset.eq_of_subset_of_card_le hsubset (by simp [hxy, hcard])
      exact Set.mem_singleton_iff.mpr heq
    · rintro rfl
      exact ⟨hT, hU⟩
  have unitBottom (c : GaussianInt) :
      {c, c + 1} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    refine ⟨c, Or.inl ⟨rfl, Or.inl ⟨by simp, ?_⟩⟩⟩
    simp [Zsqrtd.ext_iff]
  have unitLeft (c : GaussianInt) :
      {c, c + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    refine ⟨c, Or.inr ⟨rfl, Or.inl ⟨by simp, ?_⟩⟩⟩
    simp []
  have unitRight (c : GaussianInt) :
      {c + 1, c + 1 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
    refine ⟨c + 1, Or.inr ⟨rfl, Or.inr ⟨?_, by simp⟩⟩⟩
    simp []
  refine ⟨finish D a (a + 1) (a + 1 + ⟨0, 1⟩) da (by simp [Zsqrtd.ext_iff])
      ?_ (unitRight a) ?_,
    finish Eminus a a (a + 1) dma (by simp [])
      ?_ (unitBottom a) ?_,
    finish D b b (b + ⟨0, 1⟩) db (by simp [Zsqrtd.ext_iff])
      ?_ (unitLeft b) ?_,
    finish Eplus b b (b + 1) dpb (by simp [])
      ?_ (unitBottom b) ?_⟩
  · exact ⟨a + 1, Or.inr ⟨rfl, Or.inl ⟨dleft, by simpa using da⟩⟩⟩
  · intro v hv hu
    have ht := dBounds v hv
    have hh := unitBounds a v hu
    simp [a, Zsqrtd.ext_iff] at hh ⊢
    omega
  · exact ⟨a, Or.inl ⟨rfl, Or.inr ⟨dma, emtop⟩⟩⟩
  · intro v hv hu
    have ht := eBounds _ rfl v hv
    have hh := unitBounds a v hu
    simp [a, Zsqrtd.ext_iff] at hh ⊢
    omega
  · exact ⟨b, Or.inr ⟨rfl, Or.inr ⟨db, dright⟩⟩⟩
  · intro v hv hu
    have ht := dBounds v hv
    have hh := unitBounds b v hu
    simp [b, Zsqrtd.ext_iff] at hh ⊢
    omega
  · exact ⟨b, Or.inl ⟨rfl, Or.inr ⟨dpb, eptop⟩⟩⟩
  · intro v hv hu
    have ht := eBounds _ rfl v hv
    have hh := unitBounds b v hu
    simp [b, Zsqrtd.ext_iff] at hh ⊢
    omega

end ApollonianSuperharmonic

end
