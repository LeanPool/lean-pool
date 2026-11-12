/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices

-- [TABLET NODE: P4062T1CanonicalSupport]

/-!
# P4062T1CanonicalSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CanonicalSupport

private theorem hcellCoord (q : Nat) (z : GaussianInt) :
      z ∈ FordCellDomain q ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := by
  classical
  constructor
  · intro hz
    change z ∈ ((Finset.range q).product (Finset.range q)).image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)) at hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, heq⟩
    have hab := Finset.mem_product.mp ha
    rcases a with ⟨m, n⟩
    have hm := Finset.mem_range.mp hab.1
    have hn := Finset.mem_range.mp hab.2
    have hre : z.re = (m : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.re) heq
      simpa using hh.symm
    have him : z.im = (n : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.im) heq
      simpa using hh.symm
    simp [hre, him, hm, hn]
  · rintro ⟨hzr, hzr', hzi, hzi'⟩
    let m := z.re.toNat
    let n := z.im.toNat
    have hmcast : (m : Int) = z.re := Int.toNat_of_nonneg hzr
    have hncast : (n : Int) = z.im := Int.toNat_of_nonneg hzi
    have hm : m < q := by
      exact_mod_cast (show (m : Int) < q by omega)
    have hn : n < q := by
      exact_mod_cast (show (n : Int) < q by omega)
    apply Finset.mem_image.mpr
    refine ⟨(m, n), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hm, Finset.mem_range.mpr hn⟩, ?_⟩
    apply Zsqrtd.ext <;> simp [hmcast, hncast]

private theorem hfootSquare (q : Nat) (hqpos : 0 < q) :
      FootprintVertices (FordTile q) = FordVertexDomain q := by
  classical
  have hc : (FordTile q).cells.Nonempty := by
    refine ⟨⟨0, 0⟩, ?_⟩
    simp only [FordTile, FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod,
        Finset.mem_image, Finset.mem_product, Finset.mem_range, Zsqrtd.mk.injEq,
        Int.natCast_eq_zero, Prod.exists, exists_eq_right_right, exists_eq_right, and_self]
    exact hqpos
  ext x
  simp only [FootprintVertices, ite_eq_left hc, FordVertexDomain,
    Set.mem_ofPred_eq]
  simp only [FordTile, FordCellDomain, Finset.mem_image,
    ]
  constructor
  · rintro ⟨z, ⟨a, ha, hz⟩, hcorner⟩
    rcases a with ⟨m, n⟩
    have hab := Finset.mem_product.mp ha
    have hm := Finset.mem_range.mp hab.1
    have hn := Finset.mem_range.mp hab.2
    have hre : z.re = (m : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.re) hz
      simpa using hh.symm
    have him : z.im = (n : Int) := by
      have hh := congrArg (fun w : GaussianInt => w.im) hz
      simpa using hh.symm
    rcases hcorner with rfl | rfl | rfl | rfl
    all_goals simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one,
      Zsqrtd.im_one, hre, him] at *
    all_goals omega
  · intro hx
    rcases hx with ⟨hxre0, hxreq, hxim0, hximq⟩
    let m := min x.re.toNat (q - 1)
    let n := min x.im.toNat (q - 1)
    have hcastre : (x.re.toNat : Int) = x.re := Int.toNat_of_nonneg hxre0
    have hcastim : (x.im.toNat : Int) = x.im := Int.toNat_of_nonneg hxim0
    have hmlt : m < q := by dsimp [m]; omega
    have hnlt : n < q := by dsimp [n]; omega
    have hmcase : (m : Int) = x.re ∨ (m : Int) + 1 = x.re := by
      by_cases h : x.re.toNat ≤ q - 1
      · left
        dsimp [m]
        rw [Nat.min_eq_left h, hcastre]
      · right
        have hqle : (x.re.toNat : Int) ≤ q := by omega
        have hqminus : (q - 1 : Int) < x.re.toNat := by omega
        have hxeq : x.re = q := by omega
        have hmin : min x.re.toNat (q - 1) = q - 1 := by omega
        dsimp [m]
        rw [hmin, hxeq]
        omega
    have hncase : (n : Int) = x.im ∨ (n : Int) + 1 = x.im := by
      by_cases h : x.im.toNat ≤ q - 1
      · left
        dsimp [n]
        rw [Nat.min_eq_left h, hcastim]
      · right
        have hqle : (x.im.toNat : Int) ≤ q := by omega
        have hqminus : (q - 1 : Int) < x.im.toNat := by omega
        have hxeq : x.im = q := by omega
        have hmin : min x.im.toNat (q - 1) = q - 1 := by omega
        dsimp [n]
        rw [hmin, hxeq]
        omega
    let z : GaussianInt := ⟨m, n⟩
    have hzmem : z ∈ FordCellDomain q := by
      apply Finset.mem_image.mpr
      refine ⟨(m, n), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hmlt, Finset.mem_range.mpr hnlt⟩, ?_⟩
      rfl
    have hxcorner : x = z ∨ x = z + 1 ∨
        x = z + ⟨0, 1⟩ ∨ x = z + 1 + ⟨0, 1⟩ := by
      rcases hmcase with hm | hm <;> rcases hncase with hn | hn
      · left
        apply Zsqrtd.ext <;> simp [z, hm, hn]
      · right; right; left
        apply Zsqrtd.ext <;> simp [z, hm, hn]
      · right; left
        apply Zsqrtd.ext <;> simp [z, hm, hn]
      · right; right; right
        apply Zsqrtd.ext <;> simp [z, hm, hn]
    refine ⟨z, ?_, hxcorner⟩
    simpa [FordTile, FordCellDomain] using hzmem

private theorem hFcells (q : Nat) (hqpos : 0 < q) : (FordTile q).cells.Nonempty := by
  classical
  refine ⟨⟨0, 0⟩, ?_⟩
  simp only [FordTile, FordCellDomain, Int.reduceNeg, Finset.product_eq_sprod,
      Finset.mem_image, Finset.mem_product, Finset.mem_range, Zsqrtd.mk.injEq,
      Int.natCast_eq_zero, Prod.exists, exists_eq_right_right, exists_eq_right, and_self]
  exact hqpos

private theorem hcellTiles (q : Nat) (z : GaussianInt) :
      z ∈ (FordTile q).cells ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := by
  classical
  have hcellCoord (z : GaussianInt) :
      z ∈ FordCellDomain q ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := hcellCoord q z
  change z ∈ FordCellDomain q ↔ _
  exact hcellCoord z

private theorem hhoriz (q : Nat) (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∈ (FordTile q).cells)) ↔
      0 ≤ z.re ∧ z.re < (q : Int) ∧
        (z.im = 0 ∨ z.im = q) := by
  classical
  have hcellTiles (z : GaussianInt) :
      z ∈ (FordTile q).cells ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := hcellTiles q z
  rw [hcellTiles z, hcellTiles (z - ⟨0, 1⟩)]
  simp
  omega

private theorem hvert (q : Nat) (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - 1 ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - 1 ∈ (FordTile q).cells)) ↔
      0 ≤ z.im ∧ z.im < (q : Int) ∧
        (z.re = 0 ∨ z.re = q) := by
  classical
  have hcellTiles (z : GaussianInt) :
      z ∈ (FordTile q).cells ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := hcellTiles q z
  rw [hcellTiles z, hcellTiles (z - 1)]
  simp
  omega

private theorem hboundarySquare (q : Nat) (hqpos : 0 < q) :
      BoundaryFootprintVertices (FordTile q) =
        {x | 0 ≤ x.re ∧ x.re ≤ (q : Int) ∧
          0 ≤ x.im ∧ x.im ≤ (q : Int) ∧
          (x.re = 0 ∨ x.re = (q : Int) ∨
            x.im = 0 ∨ x.im = (q : Int))} := by
  classical
  have hFcells : (FordTile q).cells.Nonempty := hFcells q hqpos
  have hhoriz (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∈ (FordTile q).cells)) ↔
      0 ≤ z.re ∧ z.re < (q : Int) ∧
        (z.im = 0 ∨ z.im = q) := hhoriz q z
  have hvert (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - 1 ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - 1 ∈ (FordTile q).cells)) ↔
      0 ≤ z.im ∧ z.im < (q : Int) ∧
        (z.re = 0 ∨ z.re = q) := hvert q z
  ext x
  constructor
  · intro hx
    change 0 ≤ x.re ∧ x.re ≤ (q : Int) ∧
      0 ≤ x.im ∧ x.im ≤ (q : Int) ∧
      (x.re = 0 ∨ x.re = (q : Int) ∨
        x.im = 0 ∨ x.im = (q : Int))
    simp only [BoundaryFootprintVertices, ite_eq_left hFcells,
      Set.mem_ofPred_eq] at hx
    rcases hx with ⟨e, he, hxe⟩
    change ∃ z, (e = {z, z + 1} ∧
      ((z ∈ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∈ (FordTile q).cells))) ∨
      (e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ (FordTile q).cells ∧ z - 1 ∉ (FordTile q).cells) ∨
          (z ∉ (FordTile q).cells ∧ z - 1 ∈ (FordTile q).cells))) at he
    rcases he with ⟨z, hz⟩
    rcases hz with ⟨rfl, hxor⟩ | ⟨rfl, hxor⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      have hside := (hhoriz z).mp hxor
      rcases hside with ⟨hzr, hzru, hside⟩
      rcases hxe with hxe | hxe
      · have hr := congrArg (fun w : GaussianInt => w.re) hxe
        have hi := congrArg (fun w : GaussianInt => w.im) hxe
        rw [hr, hi]
        rcases hside with hside | hside <;> omega
      · have hr := congrArg (fun w : GaussianInt => w.re) hxe
        have hi := congrArg (fun w : GaussianInt => w.im) hxe
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one] at hr hi
        rw [hr, hi]
        rcases hside with hside | hside <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      have hside := (hvert z).mp hxor
      rcases hside with ⟨hzi, hziu, hside⟩
      rcases hxe with hxe | hxe
      · have hr := congrArg (fun w : GaussianInt => w.re) hxe
        have hi := congrArg (fun w : GaussianInt => w.im) hxe
        simp only [hr, hi]
        rcases hside with hside | hside <;> omega
      · have hr := congrArg (fun w : GaussianInt => w.re) hxe
        have hi := congrArg (fun w : GaussianInt => w.im) hxe
        simp only [Zsqrtd.re_add, Zsqrtd.im_add,
          ] at hr hi
        rw [hr, hi]
        rcases hside with hside | hside <;> omega
  · rintro ⟨hxre0, hxreq, hxim0, hximq, hside⟩
    have hhorizontal (hs : x.im = 0 ∨ x.im = q) :
        ∃ e, e ∈ BoundaryFootprintEdges (FordTile q) ∧ x ∈ e := by
      by_cases hlt : x.re < q
      · let z := x
        have hcond : 0 ≤ z.re ∧ z.re < q ∧
            (z.im = 0 ∨ z.im = q) := by simpa [z] using And.intro hxre0 (And.intro hlt hs)
        refine ⟨{z, z + 1}, ?_, ?_⟩
        · change ∃ w, _
          exact ⟨z, Or.inl ⟨rfl, (hhoriz z).mpr hcond⟩⟩
        · simp [z]
      · have hxeq : x.re = q := by omega
        let z := x - 1
        have hcond : 0 ≤ z.re ∧ z.re < q ∧
            (z.im = 0 ∨ z.im = q) := by
          simpa [z, hxeq] using And.intro (show 0 ≤ x.re - 1 by omega)
            (And.intro (show x.re - 1 < q by omega) (by simp [hs]))
        refine ⟨{z, z + 1}, ?_, ?_⟩
        · change ∃ w, _
          exact ⟨z, Or.inl ⟨rfl, (hhoriz z).mpr hcond⟩⟩
        · simp [z]
    have hvertical (hs : x.re = 0 ∨ x.re = q) :
        ∃ e, e ∈ BoundaryFootprintEdges (FordTile q) ∧ x ∈ e := by
      by_cases hlt : x.im < q
      · let z := x
        have hcond : 0 ≤ z.im ∧ z.im < q ∧
            (z.re = 0 ∨ z.re = q) := by simpa [z] using And.intro hxim0 (And.intro hlt hs)
        refine ⟨{z, z + ⟨0, 1⟩}, ?_, ?_⟩
        · change ∃ w, _
          exact ⟨z, Or.inr ⟨rfl, (hvert z).mpr hcond⟩⟩
        · simp [z]
      · have hxeq : x.im = q := by omega
        let z := x - ⟨0, 1⟩
        have hcond : 0 ≤ z.im ∧ z.im < q ∧
            (z.re = 0 ∨ z.re = q) := by
          simpa [z, hxeq] using And.intro (show 0 ≤ x.im - 1 by omega)
            (And.intro (show x.im - 1 < q by omega) (by simp [hs]))
        refine ⟨{z, z + ⟨0, 1⟩}, ?_, ?_⟩
        · change ∃ w, _
          exact ⟨z, Or.inr ⟨rfl, (hvert z).mpr hcond⟩⟩
        · simp [z]
    simp only [BoundaryFootprintVertices, ite_eq_left hFcells,
      Set.mem_ofPred_eq]
    rcases hside with hside | hside | hside | hside
    · obtain ⟨e, he, hx⟩ := hvertical (Or.inl hside)
      exact ⟨e, he, hx⟩
    · obtain ⟨e, he, hx⟩ := hvertical (Or.inr hside)
      exact ⟨e, he, hx⟩
    · obtain ⟨e, he, hx⟩ := hhorizontal (Or.inl hside)
      exact ⟨e, he, hx⟩
    · obtain ⟨e, he, hx⟩ := hhorizontal (Or.inr hside)
      exact ⟨e, he, hx⟩

end CanonicalSupport

theorem P4062T1CanonicalSupport (q : Nat) (hqpos : 0 < q) :
    FootprintVertices (FordTile q) = FordVertexDomain q ∧
    BoundaryFootprintVertices (FordTile q) =
      {x | 0 ≤ x.re ∧ x.re ≤ (q : Int) ∧
        0 ≤ x.im ∧ x.im ≤ (q : Int) ∧
        (x.re = 0 ∨ x.re = (q : Int) ∨ x.im = 0 ∨ x.im = (q : Int))} := by
-- BODY
  classical
  have hcellCoord (z : GaussianInt) :
      z ∈ FordCellDomain q ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := CanonicalSupport.hcellCoord q z
  have hfootSquare :
      FootprintVertices (FordTile q) = FordVertexDomain q := CanonicalSupport.hfootSquare q hqpos
  have hFcells : (FordTile q).cells.Nonempty := CanonicalSupport.hFcells q hqpos
  have hcellTiles (z : GaussianInt) :
      z ∈ (FordTile q).cells ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧
          0 ≤ z.im ∧ z.im < (q : Int) := CanonicalSupport.hcellTiles q z
  have hhoriz (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - ⟨0, 1⟩ ∈ (FordTile q).cells)) ↔
      0 ≤ z.re ∧ z.re < (q : Int) ∧
        (z.im = 0 ∨ z.im = q) := CanonicalSupport.hhoriz q z
  have hvert (z : GaussianInt) :
      ((z ∈ (FordTile q).cells ∧ z - 1 ∉ (FordTile q).cells) ∨
        (z ∉ (FordTile q).cells ∧ z - 1 ∈ (FordTile q).cells)) ↔
      0 ≤ z.im ∧ z.im < (q : Int) ∧
        (z.re = 0 ∨ z.re = q) := CanonicalSupport.hvert q z
  have hboundarySquare :
      BoundaryFootprintVertices (FordTile q) =
        {x | 0 ≤ x.re ∧ x.re ≤ (q : Int) ∧
          0 ≤ x.im ∧ x.im ≤ (q : Int) ∧
          (x.re = 0 ∨ x.re = (q : Int) ∨
            x.im = 0 ∨ x.im = (q : Int))} := CanonicalSupport.hboundarySquare q hqpos
  exact ⟨hfootSquare, hboundarySquare⟩

end ApollonianSuperharmonic

end
