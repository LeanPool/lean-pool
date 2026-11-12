/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4456T2EdgeInterior
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.P4456T2VertexInterior
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4456T2SquareEdges]

/-!
# P4456T2SquareEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SquareEdgeProof

private theorem hcell :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (T.cells = (TileTranslation
            (FordTile n)
            w).cells) → (((TileTranslation (FordTile n) w).cells = (FordCellDomain n).image
            (GaussianTranslation w)) → (∀ (c : GaussianInt), c ∈ T.cells ↔ ∃ (a : ℕ) (b : ℕ), a <
                n ∧
            b < n ∧ c = w + ⟨(↑a : ℤ), (↑b : ℤ)⟩)) ) := by
  classical
  intro n w T hcells htrans c
  rw [hcells, htrans]
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨z, hzdom, heq⟩
    rcases Finset.mem_image.mp hzdom with ⟨p, hp, hpz⟩
    rcases p with ⟨a, b⟩
    subst z
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have ha := Finset.mem_range.mp ha
    have hb := Finset.mem_range.mp hb
    have heq' : GaussianTranslation w
        (⟨(a : Int), (b : Int)⟩ : GaussianInt) = c := by simpa [GaussianTranslation] using heq
    exact ⟨a, b, ha, hb, by simpa [GaussianTranslation, add_comm] using heq'.symm⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    rw [hc]
    apply Finset.mem_image.mpr
    refine ⟨(⟨(a : Int), (b : Int)⟩ : GaussianInt), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(a,b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha,
        Finset.mem_range.mpr hb⟩, rfl⟩
    · simp [GaussianTranslation, add_comm]

private theorem hnonempty :
    (by
      classical
      exact
        ∀ (n : Nat), ((0 : ℕ) < n) → (∀ (w : GaussianInt), ∀ (T : ProtoTile), (T.cells =
            (TileTranslation (FordTile n) w).cells) → (((TileTranslation (FordTile n) w).cells =
            (FordCellDomain n).image (GaussianTranslation w)) → (T.cells.Nonempty))) ) := by
  classical
  intro n hn w T hcells htrans
  rw [hcells, htrans]
  apply Finset.image_nonempty.mpr
  refine ⟨(⟨(0 : Int), (0 : Int)⟩ : GaussianInt), ?_⟩
  change (⟨(0 : Int), (0 : Int)⟩ : GaussianInt) ∈
    Finset.image (fun p : Nat × Nat =>
      (⟨(p.1 : Int), (p.2 : Int)⟩ : GaussianInt))
      ((Finset.range n).product (Finset.range n))
  apply Finset.mem_image.mpr
  refine ⟨(0,0), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_range.mpr hn
  · exact Finset.mem_range.mpr hn

private theorem hvertex_coords :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (c : GaussianInt), c ∈ T.cells ↔ ∃ a
            b : Nat, a < n ∧ b < n ∧ c = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) →
            ((T.cells.Nonempty) → (∀ v ∈ FootprintVertices T, ∃ (a : ℕ) (b : ℕ), a ≤ n ∧ b ≤ n ∧ v =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩)) ) := by
  classical
  intro n w T hcell hnonempty v hv
  unfold FootprintVertices at hv
  rw [ite_eq_left hnonempty] at hv
  rcases hv with ⟨c, hc, hcorner⟩
  rcases hcell c |>.mp hc with ⟨a,b,ha,hb,hcw⟩
  rcases hcorner with h | h | h | h
  · subst v
    refine ⟨a,b, Nat.le_of_lt ha, Nat.le_of_lt hb, ?_⟩
    simp [hcw]
  · subst v
    refine ⟨a+1,b, ?_, Nat.le_of_lt hb, ?_⟩
    · exact Nat.succ_le_of_lt ha
    · rw [hcw]
      apply Zsqrtd.ext <;> simp; ring
  · subst v
    refine ⟨a,b+1, Nat.le_of_lt ha, ?_, ?_⟩
    · exact Nat.succ_le_of_lt hb
    · simp [hcw, add_assoc]
  · subst v
    refine ⟨a+1,b+1, Nat.succ_le_of_lt ha, Nat.succ_le_of_lt hb, ?_⟩
    rw [hcw]
    apply Zsqrtd.ext <;> simp <;> ring

private theorem hvertex_box :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (c : GaussianInt), c ∈ T.cells ↔ ∃ a
            b : Nat, a < n ∧ b < n ∧ c = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) →
            ((T.cells.Nonempty) → (∀ v ∈ FootprintVertices T, w.re ≤ v.re ∧ v.re ≤ w.re + (↑n : ℤ) ∧
            w.im ≤ v.im ∧ v.im ≤ w.im + (↑n : ℤ))) ) := by
  classical
  intro n w T hcell hnonempty v hv
  unfold FootprintVertices at hv
  rw [ite_eq_left hnonempty] at hv
  rcases hv with ⟨c, hc, hcorner⟩
  rcases hcell c |>.mp hc with ⟨a,b,ha,hb,hcw⟩
  rcases hcorner with h | h | h | h
  all_goals
    subst v
    rw [hcw] at *
    simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      ]
    norm_num
    have ha' : (a : Int) < n := by exact_mod_cast ha
    have hb' : (b : Int) < n := by exact_mod_cast hb
    omega

private theorem hstarCoords :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (c : GaussianInt), c ∈ T.cells ↔ ∃ a
            b : Nat, a < n ∧ b < n ∧ c = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) → (∀ (a :
                ℕ), ∀ (b : ℕ), (0 : ℕ) < a → a < n → (0 : ℕ) < b → b < n → ∀ (j : Fin (4 : ℕ)),
                LatticeVertexIncidentCell (w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) j ∈ T.cells) ) := by
  classical
  intro n w T hcell a b ha0 haN hb0 hbN
  let p : GaussianInt := w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)
  have hmem (u v : Nat) (hu : u < n) (hv : v < n) :
      w + (⟨(u : Int), (v : Int)⟩ : GaussianInt) ∈ T.cells := by
    exact (hcell _).2 ⟨u, v, hu, hv, rfl⟩
  have hA : p - 1 = w + (⟨((a - 1 : Nat) : Int), (b : Int)⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [p]; omega
  have hAB : p - 1 - ⟨0,1⟩ =
      w + (⟨((a - 1 : Nat) : Int), ((b - 1 : Nat) : Int)⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [p] <;> omega
  have hB : p - ⟨0,1⟩ =
      w + (⟨(a : Int), ((b - 1 : Nat) : Int)⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [p]; omega
  intro j
  fin_cases j
  · simpa [LatticeVertexIncidentCell, p] using hmem a b haN hbN
  · rw [LatticeVertexIncidentCell, hA]
    exact hmem (a-1) b (by omega) hbN
  · rw [LatticeVertexIncidentCell, hAB]
    exact hmem (a-1) (b-1) (by omega) (by omega)
  · rw [LatticeVertexIncidentCell, hB]
    exact hmem a (b-1) haN (by omega)

private theorem hEdgeH :
    (by
      classical
      exact
        ∀ (n : Nat), ((0 : ℕ) < n) → (∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (a : Nat), ∀ (b
            : Nat), (a < n) → ((b < n) → (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) ∈ T.cells)))
            → (∀ (a : ℕ), ∀ (b : ℕ), a < n → b ≤ n → {w + ⟨(↑a : ℤ), (↑b : ℤ)⟩, w + ⟨(↑(a + (1 :
            ℕ)) : ℤ),
            (↑b : ℤ)⟩} ∈ FootprintEdges T)) ) := by
  classical
  intro n hn w T hmem a b ha hb
  change ∃ c ∈ T.cells,
    ({w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
      w + (⟨((a+1 : Nat) : Int), (b : Int)⟩ : GaussianInt)} : Finset GaussianInt) =
        {c, c + 1} ∨ _ = {c, c + ⟨0,1⟩} ∨
          _ = {c+1, c+1+⟨0,1⟩} ∨ _ = {c+⟨0,1⟩, c+1+⟨0,1⟩}
  by_cases hb' : b < n
  · refine ⟨w + (⟨(a : Int), (b : Int)⟩ : GaussianInt), hmem a b ha hb', Or.inl ?_⟩
    apply Finset.ext
    intro q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    apply Iff.intro
    · rintro (rfl | rfl) <;> simp [Zsqrtd.ext_iff]; omega
    · rintro (rfl | rfl) <;> simp [Zsqrtd.ext_iff]; omega
  · have hb'lt : b = n := by omega
    let c : GaussianInt := w + (⟨(a : Int), ((b-1 : Nat) : Int)⟩ : GaussianInt)
    have hc : c ∈ T.cells := by
      apply hmem
      · exact ha
      · omega
    refine ⟨c, hc, Or.inr (Or.inr (Or.inr ?_))⟩
    apply Finset.ext
    intro q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [c, hb'lt, Zsqrtd.ext_iff] <;> omega
    · rintro (rfl | rfl) <;> simp [c, hb'lt, Zsqrtd.ext_iff] <;> omega

private theorem hEdgeV :
    (by
      classical
      exact
        ∀ (n : Nat), ((0 : ℕ) < n) → (∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (a : Nat), ∀ (b
            : Nat), (a < n) → ((b < n) → (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) ∈ T.cells)))
            → (∀ (a : ℕ), ∀ (b : ℕ), a ≤ n → b < n → {w + ⟨(↑a : ℤ), (↑b : ℤ)⟩, w + ⟨(↑a : ℤ),
            (↑(b + (1 : ℕ)) : ℤ)⟩} ∈ FootprintEdges T)) ) := by
  classical
  intro n hn w T hmem a b ha hb
  change ∃ c ∈ T.cells,
    ({w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
      w + (⟨(a : Int), ((b+1 : Nat) : Int)⟩ : GaussianInt)} : Finset GaussianInt) =
        {c, c + 1} ∨ _ = {c, c + ⟨0,1⟩} ∨
          _ = {c+1, c+1+⟨0,1⟩} ∨ _ = {c+⟨0,1⟩, c+1+⟨0,1⟩}
  by_cases ha' : a < n
  · refine ⟨w + (⟨(a : Int), (b : Int)⟩ : GaussianInt), hmem a b ha' hb, Or.inr (Or.inl ?_)⟩
    apply Finset.ext
    intro q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [Zsqrtd.ext_iff]; omega
    · rintro (rfl | rfl) <;> simp [Zsqrtd.ext_iff]; omega
  · have ha'lt : a = n := by omega
    let c : GaussianInt := w + (⟨((a-1 : Nat) : Int), (b : Int)⟩ : GaussianInt)
    have hc : c ∈ T.cells := by
      apply hmem
      · omega
      · exact hb
    refine ⟨c, hc, Or.inr (Or.inr (Or.inl ?_))⟩
    apply Finset.ext
    intro q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [c, ha'lt, Zsqrtd.ext_iff] <;> omega
    · rintro (rfl | rfl) <;> simp [c, ha'lt, Zsqrtd.ext_iff] <;> omega

private theorem hzv :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ((x =
            z +
            (1 : GaussianInt) ∧ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
            GaussianInt) ∧ x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ v = z + (1 :
            GaussianInt) ∨ (x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = z + ⟨(0 : ℤ), (1 :
            ℤ)⟩ ∨ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = z + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ v =
            z + ⟨(0 : ℤ), (1 : ℤ)⟩) → (z ≠ v) ) := by
  classical
  intro x y z v hform heq
  rcases hform with ⟨_, hvform⟩ | ⟨_, hvform⟩
  · rw [hvform] at heq
    have heq' : z + 0 = z + 1 := by simp at heq
    have hzero : (0 : GaussianInt) = 1 := add_left_cancel heq'
    norm_num at hzero
  · rw [hvform] at heq
    have heq' : z + 0 = z + ⟨0,1⟩ := by simpa using heq
    have hzero : (0 : GaussianInt) = ⟨0,1⟩ := add_left_cancel heq'
    have hr := congrArg Zsqrtd.im hzero
    norm_num at hr

private theorem hcoordsAt320 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ∀ (a : ℕ), ∀ (b :
            ℕ), (z = w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (v = w + ⟨(↑c : ℤ), (↑d :
            ℤ)⟩) →
            ((v = z + (1 : GaussianInt)) → (c = a + 1 ∧ d = b)))) ) := by
  classical
  intro n w z v a b hza c d hvc hvform
  have heq' : w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) = z + 1 := by
    rw [← hvc, hvform]
  rw [hza] at heq'
  have heq := congrArg Zsqrtd.re heq'
  have him := congrArg Zsqrtd.im heq'
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at heq him
  norm_num at heq him
  constructor <;> omega

private theorem hcoordsAt367 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ∀ (a : ℕ), ∀ (b :
            ℕ), (z = w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (v = w + ⟨(↑c : ℤ), (↑d :
            ℤ)⟩) →
            ((v = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → (c = a ∧ d = b + 1)))) ) := by
  classical
  intro n w z v a b hza c d hvc hvform
  have heq' : w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) = z + ⟨0,1⟩ := by
    rw [← hvc, hvform]
  rw [hza] at heq'
  have heq := congrArg Zsqrtd.re heq'
  have him := congrArg Zsqrtd.im heq'
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at heq him
  norm_num at heq him
  constructor <;> omega

end SquareEdgeProof

namespace SquareEdgeDetails

private theorem htrans :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), (TileTranslation (FordTile n) w).cells =
            (FordCellDomain n).image (GaussianTranslation w) ) := by
  classical
  intro n w
  exact (TileTranslationFormulas (FordTile n) w).1

private theorem hmem :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (c : GaussianInt), c ∈ T.cells ↔
            ∃ a b : Nat, a < n ∧ b < n ∧ c = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) → (∀ (a
            : ℕ), ∀ (b : ℕ), a < n → b < n → w + ⟨(↑a : ℤ), (↑b : ℤ)⟩ ∈ T.cells) ) := by
  classical
  intro n w T hcell a b ha hb
  exact (hcell _).2 ⟨a, b, ha, hb, rfl⟩

private theorem hAedge :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ((x =
            z + (1 : GaussianInt) ∧ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
            GaussianInt) ∧ x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ v = z + (1 :
            GaussianInt) ∨ (x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = z + ⟨(0 : ℤ), (1
            : ℤ)⟩ ∨ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = z + ⟨(0 : ℤ), (1 : ℤ)⟩)
            ∧ v = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → (
        let A : ProtoTile := ⟨{z}, z⟩
        ({x,y} : Finset GaussianInt) ∈ FootprintEdges A) ) := by
  classical
  intro x y z v hform A
  have h := (P4397T1UnitEdgeCells.2 x y z v hform A).1
  apply h.mpr
  simp [A]

private theorem hBedge :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ((x =
            z + (1 : GaussianInt) ∧ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
            GaussianInt) ∧ x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ v = z + (1 :
            GaussianInt) ∨ (x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = z + ⟨(0 : ℤ), (1
            : ℤ)⟩ ∨ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = z + ⟨(0 : ℤ), (1 : ℤ)⟩)
            ∧ v = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → (
        let B : ProtoTile := ⟨{v}, v⟩
        ({x,y} : Finset GaussianInt) ∈ FootprintEdges B) ) := by
  classical
  intro x y z v hform B
  have h := (P4397T1UnitEdgeCells.2 x y z v hform B).1
  apply h.mpr
  simp [B]

private theorem hpcoordsAt429 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (z = w + ⟨(↑a : ℤ), (↑b :
            ℤ)⟩) → (
        let pa : Nat := a + 1
        let p : GaussianInt := if 0 < b then z + 1 else z + 1 + ⟨0,1⟩
        let pb : Nat := if 0 < b then b else b + 1
        p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt)) ) := by
  classical
  intro w z a b hza pa p pb
  dsimp [p, pa, pb]
  split_ifs <;> rw [hza] <;> apply Zsqrtd.ext <;> simp <;> ring

private theorem hcoordsNAt432 :
    (by
      classical
      exact
        ∀ (n : Nat), ((0 : ℕ) < n) → (∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (c < n) → ((c =
            a + 1 ∧ d = b) → (1 < n))) ) := by
  classical
  intro n hn a b c d hc hcoords
  have hc' : (c : Int) < n := by exact_mod_cast hc
  rw [hcoords.1] at hc'
  omega

private theorem hpstrictAt436 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (a : ℕ), ∀ (b : ℕ), (b < n) → (∀ (c : ℕ), ∀ (d : ℕ), (c < n) → ((c = a + 1
            ∧ d = b) → (
        let pa : Nat := a + 1
        let pb : Nat := if 0 < b then b else b + 1
        (1 < n) → (0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n)))) ) := by
  classical
  intro n a b hb c d hc hcoords pa pb hcoordsN
  dsimp [pa, pb]
  split_ifs <;> omega

private theorem hpIsEndAt439 :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (b : ℕ), (x = z + (1 :
            GaussianInt) ∧ y = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
            GaussianInt) ∧ x = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) → (
        let p : GaussianInt := if 0 < b then z + 1 else z + 1 + ⟨0,1⟩
        p = x ∨ p = y) ) := by
  classical
  intro x y z b hor p
  rcases hor with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · dsimp [p]
    split_ifs with hbpos <;> simp [hx, hy]
  · dsimp [p]
    split_ifs with hbpos <;> simp [hx, hy]

private theorem hpFootAt445 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (v :
            GaussianInt), (({x, y} ∈ FootprintEdges T ↔ z ∈ T.cells ∨ v ∈ T.cells) ∧ ({x, y} ∈
            BoundaryFootprintEdges T ↔ z ∈ T.cells ∧ v ∉ T.cells ∨ z ∉ T.cells ∧ v ∈ T.cells) ∧
            (z ∈ T.cells ∨ v ∈ T.cells → x ∈ FootprintVertices T ∧ y ∈ FootprintVertices T ∧ ∀ (t
            : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (((1 : ℝ) - (↑t : ℝ)) * (↑x.re : ℝ) + (↑t :
            ℝ) * (↑y.re : ℝ), ((1 : ℝ) - (↑t : ℝ)) * (↑x.im : ℝ) + (↑t : ℝ) * (↑y.im : ℝ)) ∈
            TileRealization T) ∧ (z ∈ T.cells ∧ v ∈ T.cells → OpenLatticeEdge x y ⊆ interior
            (TileRealization T)) ∧ ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            T.cells) → z ∈ T.cells ∧ v ∈ T.cells)) → ((z ∈ T.cells) → (∀ (b : ℕ),
        let p : GaussianInt := if 0 < b then z + 1 else z + 1 + ⟨0,1⟩
        (p = x ∨ p = y) → (p ∈ FootprintVertices T))) ) := by
  classical
  intro T x y z v hedgeInfo hz b p hpIsEnd
  have hends := hedgeInfo.2.2.1 (Or.inl hz)
  rcases hpIsEnd with h | h
  · rw [h]
    exact hends.1
  · rw [h]
    exact hends.2.1

private theorem hstarAt452 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (a : Nat), ∀ (b : Nat), (0 < a) →
            ((a < n) → ((0 < b) → ((b < n) → (∀ j : Fin 4, LatticeVertexIncidentCell (w + (⟨(a :
            Int), (b : Int)⟩ : GaussianInt)) j ∈ T.cells))))) → (∀ (z : GaussianInt), ∀ (a : ℕ),
            ∀ (b : ℕ),
        let pa : Nat := a + 1
        let p : GaussianInt := if 0 < b then z + 1 else z + 1 + ⟨0,1⟩
        let pb : Nat := if 0 < b then b else b + 1
        (p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt)) → ((0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n)
            → (∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ T.cells))) ) := by
  classical
  intro n w T hstarCoords z a b pa p pb hpcoords hpstrict
  have hs := hstarCoords pa pb hpstrict.1 hpstrict.2.1
    hpstrict.2.2.1 hpstrict.2.2.2
  simpa [hpcoords] using hs

private theorem hpcoordsAt468 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (z = w + ⟨(↑a : ℤ), (↑b :
            ℤ)⟩) → (
        let pa : Nat := if 0 < a then a else a + 1
        let pb : Nat := b + 1
        let p : GaussianInt := if 0 < a then z + ⟨0,1⟩ else z + 1 + ⟨0,1⟩
        p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt)) ) := by
  classical
  intro w z a b hza pa pb p
  dsimp [p, pa, pb]
  split_ifs <;> rw [hza] <;> apply Zsqrtd.ext <;> simp <;> ring

private theorem hcoordsNAt471 :
    (by
      classical
      exact
        ∀ (n : Nat), ((0 : ℕ) < n) → (∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (d < n) → ((c =
            a ∧ d = b + 1) → (1 < n))) ) := by
  classical
  intro n hn a b c d hd hcoords
  have hd' : (d : Int) < n := by exact_mod_cast hd
  rw [hcoords.2] at hd'
  omega

private theorem hpstrictAt475 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (a : ℕ), ∀ (b : ℕ), (a < n) → (∀ (c : ℕ), ∀ (d : ℕ), (d < n) → ((c = a ∧ d
            = b + 1) → (
        let pa : Nat := if 0 < a then a else a + 1
        let pb : Nat := b + 1
        (1 < n) → (0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n)))) ) := by
  classical
  intro n a b ha c d hd hcoords pa pb hcoordsN
  dsimp [pa, pb]
  split_ifs <;> omega

private theorem hpIsEndAt478 :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (a : ℕ), (x = z + (1 :
            GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ y = z + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ y = z + (1 :
            GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ x = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → (
        let p : GaussianInt := if 0 < a then z + ⟨0,1⟩ else z + 1 + ⟨0,1⟩
        p = x ∨ p = y) ) := by
  classical
  intro x y z a hor p
  rcases hor with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · dsimp [p]
    split_ifs with hapos <;> simp [hx, hy]
  · dsimp [p]
    split_ifs with hapos <;> simp [hx, hy]

private theorem hpFootAt484 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (v :
            GaussianInt), (({x, y} ∈ FootprintEdges T ↔ z ∈ T.cells ∨ v ∈ T.cells) ∧ ({x, y} ∈
            BoundaryFootprintEdges T ↔ z ∈ T.cells ∧ v ∉ T.cells ∨ z ∉ T.cells ∧ v ∈ T.cells) ∧
            (z ∈ T.cells ∨ v ∈ T.cells → x ∈ FootprintVertices T ∧ y ∈ FootprintVertices T ∧ ∀ (t
            : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (((1 : ℝ) - (↑t : ℝ)) * (↑x.re : ℝ) + (↑t :
            ℝ) * (↑y.re : ℝ), ((1 : ℝ) - (↑t : ℝ)) * (↑x.im : ℝ) + (↑t : ℝ) * (↑y.im : ℝ)) ∈
            TileRealization T) ∧ (z ∈ T.cells ∧ v ∈ T.cells → OpenLatticeEdge x y ⊆ interior
            (TileRealization T)) ∧ ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            T.cells) → z ∈ T.cells ∧ v ∈ T.cells)) → ((z ∈ T.cells) → (∀ (a : ℕ),
        let p : GaussianInt := if 0 < a then z + ⟨0,1⟩ else z + 1 + ⟨0,1⟩
        (p = x ∨ p = y) → (p ∈ FootprintVertices T))) ) := by
  classical
  intro T x y z v hedgeInfo hz a p hpIsEnd
  have hends := hedgeInfo.2.2.1 (Or.inl hz)
  rcases hpIsEnd with h | h
  · rw [h]
    exact hends.1
  · rw [h]
    exact hends.2.1

private theorem hstarAt491 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (∀ (a : Nat), ∀ (b : Nat), (0 < a) →
            ((a < n) → ((0 < b) → ((b < n) → (∀ j : Fin 4, LatticeVertexIncidentCell (w + (⟨(a :
            Int), (b : Int)⟩ : GaussianInt)) j ∈ T.cells))))) → (∀ (z : GaussianInt), ∀ (a : ℕ),
            ∀ (b : ℕ),
        let pa : Nat := if 0 < a then a else a + 1
        let pb : Nat := b + 1
        let p : GaussianInt := if 0 < a then z + ⟨0,1⟩ else z + 1 + ⟨0,1⟩
        (p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt)) → ((0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n)
            → (∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ T.cells))) ) := by
  classical
  intro n w T hstarCoords z a b pa pb p hpcoords hpstrict
  have hs := hstarCoords pa pb hpstrict.1 hpstrict.2.1
    hpstrict.2.2.1 hpstrict.2.2.2
  simpa [hpcoords] using hs

private theorem heqAt507 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((y = x + (1 : GaussianInt)) → (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) = (w +
            (⟨(a : Int), (b : Int)⟩ : GaussianInt)) + 1))) ) := by
  classical
  intro w x y a b hxcoord c d hycoord h
  calc
    _ = y := hycoord.symm
    _ = x + 1 := h
    _ = _ := by rw [hxcoord]

private theorem hcdAt513 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (w + (⟨(c :
            Int), (d : Int)⟩ : GaussianInt) = (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) + 1) →
            (c = a + 1 ∧ d = b)) ) := by
  classical
  intro n w a b c d heq
  have hr := congrArg Zsqrtd.re heq
  have hi := congrArg Zsqrtd.im heq
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at hr hi
  norm_num at hr hi
  constructor <;> omega

private theorem hsetAt520 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((c = a + 1 ∧ d = b) → (({x,y} : Finset GaussianInt) = {w + (⟨(a : Int),
            (b : Int)⟩ : GaussianInt), w + (⟨((a+1 : Nat) : Int), (b : Int)⟩ : GaussianInt)}))) )
            := by
  classical
  intro w x y a b hxcoord c d hycoord hcd
  rw [hxcoord, hycoord, hcd.1, hcd.2]

private theorem heqAt526 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((y = x - (1 : GaussianInt)) → (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) = (w +
            (⟨(c : Int), (d : Int)⟩ : GaussianInt)) + 1))) ) := by
  classical
  intro w x y a b hxcoord c d hycoord h
  calc
    _ = x := hxcoord.symm
    _ = y + 1 := by rw [h]; simp
    _ = _ := by rw [hycoord]

private theorem hcdAt532 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (w + (⟨(a :
            Int), (b : Int)⟩ : GaussianInt) = (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt)) + 1) →
            (a = c + 1 ∧ b = d)) ) := by
  classical
  intro n w a b c d heq
  have hr := congrArg Zsqrtd.re heq
  have hi := congrArg Zsqrtd.im heq
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at hr hi
  norm_num at hr hi
  constructor <;> omega

private theorem hsetAt539 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b :
            ℕ), (x = w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d :
            ℤ)⟩) → ((a = c + 1 ∧ b = d) → (({x,y} : Finset GaussianInt) = {w + (⟨(c : Int),
            (d : Int)⟩ : GaussianInt), w + (⟨((c+1 : Nat) : Int), (d : Int)⟩ : GaussianInt)}))))
            ) := by
  classical
  intro n w x y a b hxcoord c d hycoord hcd
  rw [hxcoord, hycoord, hcd.1, hcd.2]
  apply Finset.ext
  intro q
  simp [Zsqrtd.ext_iff]; omega

private theorem heqAt548 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((y = x + ⟨(0 : ℤ), (1 : ℤ)⟩) → (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) = (w +
            (⟨(a : Int), (b : Int)⟩ : GaussianInt)) + ⟨0,1⟩))) ) := by
  classical
  intro w x y a b hxcoord c d hycoord h
  calc
    _ = y := hycoord.symm
    _ = x + ⟨0,1⟩ := h
    _ = _ := by rw [hxcoord]

private theorem hcdAt554 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (w + (⟨(c :
            Int), (d : Int)⟩ : GaussianInt) = (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) +
            ⟨0,1⟩) → (c = a ∧ d = b + 1)) ) := by
  classical
  intro n w a b c d heq
  have hr := congrArg Zsqrtd.re heq
  have hi := congrArg Zsqrtd.im heq
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at hr hi
  norm_num at hr hi
  constructor <;> omega

private theorem hsetAt561 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((c = a ∧ d = b + 1) → (({x,y} : Finset GaussianInt) = {w + (⟨(a : Int),
            (b : Int)⟩ : GaussianInt), w + (⟨(a : Int), ((b+1 : Nat) : Int)⟩ : GaussianInt)}))) )
            := by
  classical
  intro w x y a b hxcoord c d hycoord hcd
  rw [hxcoord, hycoord, hcd.1, hcd.2]

private theorem heqAt567 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), (x =
            w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d : ℤ)⟩) →
            ((y = x - ⟨(0 : ℤ), (1 : ℤ)⟩) → (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) = (w +
            (⟨(c : Int), (d : Int)⟩ : GaussianInt)) + ⟨0,1⟩))) ) := by
  classical
  intro w x y a b hxcoord c d hycoord h
  calc
    _ = x := hxcoord.symm
    _ = y + ⟨0,1⟩ := by rw [h]; simp
    _ = _ := by rw [hycoord]

private theorem hcdAt573 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (a : ℕ), ∀ (b : ℕ), ∀ (c : ℕ), ∀ (d : ℕ), (w + (⟨(a :
            Int), (b : Int)⟩ : GaussianInt) = (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt)) +
            ⟨0,1⟩) → (a = c ∧ b = d + 1)) ) := by
  classical
  intro n w a b c d heq
  have hr := congrArg Zsqrtd.re heq
  have hi := congrArg Zsqrtd.im heq
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at hr hi
  norm_num at hr hi
  constructor <;> omega

private theorem hsetAt580 :
    (by
      classical
      exact
        (Nat) → (∀ (w : GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (a : ℕ), ∀ (b :
            ℕ), (x = w + ⟨(↑a : ℤ), (↑b : ℤ)⟩) → (∀ (c : ℕ), ∀ (d : ℕ), (y = w + ⟨(↑c : ℤ), (↑d :
            ℤ)⟩) → ((a = c ∧ b = d + 1) → (({x,y} : Finset GaussianInt) = {w + (⟨(c : Int),
            (d : Int)⟩ : GaussianInt), w + (⟨(c : Int), ((d+1 : Nat) : Int)⟩ : GaussianInt)}))))
            ) := by
  classical
  intro n w x y a b hxcoord c d hycoord hcd
  rw [hxcoord, hycoord, hcd.1, hcd.2]
  apply Finset.ext
  intro q
  simp [Zsqrtd.ext_iff]; omega

end SquareEdgeDetails

theorem P4456T2SquareEdges (n : Nat) (hn : 0 < n)
    (w : GaussianInt) (T : ProtoTile)
    (hcells : T.cells = (TileTranslation (FordTile n) w).cells) :
    (∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)) ∧
    (∀ x, x ∈ FootprintVertices T → ∀ y, y ∈ FootprintVertices T →
      FourNeighborAdjacent x y → ({x, y} : Finset GaussianInt) ∈ FootprintEdges T) := by
-- BODY
  have htrans : (TileTranslation (FordTile n) w).cells =
      (FordCellDomain n).image (GaussianTranslation w) := SquareEdgeDetails.htrans n w
  have hcell (c : GaussianInt) : c ∈ T.cells ↔
      ∃ a b : Nat, a < n ∧ b < n ∧
        c = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) := SquareEdgeProof.hcell n w T hcells
            htrans c
  have hnonempty : T.cells.Nonempty := SquareEdgeProof.hnonempty n hn w T hcells htrans
  have hvertex_coords (v : GaussianInt) (hv : v ∈ FootprintVertices T) :
      ∃ a b : Nat, a ≤ n ∧ b ≤ n ∧
        v = w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) := SquareEdgeProof.hvertex_coords n w T
            hcell hnonempty v hv
  have hvertex_box (v : GaussianInt) (hv : v ∈ FootprintVertices T) :
      (w.re : Int) ≤ v.re ∧ v.re ≤ w.re + n ∧
      w.im ≤ v.im ∧ v.im ≤ w.im + n := SquareEdgeProof.hvertex_box n w T hcell hnonempty v hv
  have hstarCoords (a b : Nat) (ha0 : 0 < a) (haN : a < n)
      (hb0 : 0 < b) (hbN : b < n) :
      ∀ j : Fin 4, LatticeVertexIncidentCell
        (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) j ∈ T.cells := SquareEdgeProof.hstarCoords n
            w T hcell a b ha0 haN hb0 hbN
  have hmem (a b : Nat) (ha : a < n) (hb : b < n) :
      w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) ∈ T.cells := SquareEdgeDetails.hmem n w T hcell
          a b ha hb
  have hEdgeH (a b : Nat) (ha : a < n) (hb : b ≤ n) :
      ({w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
        w + (⟨((a+1 : Nat) : Int), (b : Int)⟩ : GaussianInt)} : Finset GaussianInt)
        ∈ FootprintEdges T := SquareEdgeProof.hEdgeH n hn w T hmem a b ha hb
  have hEdgeV (a b : Nat) (ha : a ≤ n) (hb : b < n) :
      ({w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
        w + (⟨(a : Int), ((b+1 : Nat) : Int)⟩ : GaussianInt)} : Finset GaussianInt)
        ∈ FootprintEdges T := SquareEdgeProof.hEdgeV n hn w T hmem a b ha hb
  constructor
  · intro x y hxy hxB hyB hinside
    obtain ⟨z, v, hform⟩ := P4397T1UnitEdgeCells.1 x y hxy
    let A : ProtoTile := ⟨{z}, z⟩
    let B : ProtoTile := ⟨{v}, v⟩
    have hedgeInfo := (P4397T1UnitEdgeCells.2 x y z v hform T)
    have hAedge : ({x,y} : Finset GaussianInt) ∈ FootprintEdges A := SquareEdgeDetails.hAedge x y
        z v hform
    have hBedge : ({x,y} : Finset GaussianInt) ∈ FootprintEdges B := SquareEdgeDetails.hBedge x y
        z v hform
    have hzv : z ≠ v := SquareEdgeProof.hzv x y z v hform
    have hz : z ∈ T.cells := by
      exact (P4456T2EdgeInterior T x y z v hxy hzv hAedge hBedge).1 hinside |>.1
    have hv : v ∈ T.cells := by
      exact (P4456T2EdgeInterior T x y z v hxy hzv hAedge hBedge).1 hinside |>.2
    rcases hcell z |>.mp hz with ⟨a,b,ha,hb,hza⟩
    rcases hcell v |>.mp hv with ⟨c,d,hc,hd,hvc⟩
    rcases hform with ⟨hor, hvform⟩ | ⟨hor, hvform⟩
    · have hcoords : c = a + 1 ∧ d = b := SquareEdgeProof.hcoordsAt320 n w z v a b hza c d hvc
        hvform
      let pa : Nat := a + 1
      let p : GaussianInt := if 0 < b then z + 1 else z + 1 + ⟨0,1⟩
      let pb : Nat := if 0 < b then b else b + 1
      have hpcoords : p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt) :=
          SquareEdgeDetails.hpcoordsAt429 w z a b hza
      have hcoordsN : 1 < n := SquareEdgeDetails.hcoordsNAt432 n hn a b c d hc hcoords
      have hpstrict : 0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n := SquareEdgeDetails.hpstrictAt436 n a b
          hb c d hc hcoords hcoordsN
      have hpIsEnd : p = x ∨ p = y := SquareEdgeDetails.hpIsEndAt439 x y z b hor
      have hpFoot : p ∈ FootprintVertices T := SquareEdgeDetails.hpFootAt445 T x y z v hedgeInfo
          hz b hpIsEnd
      have hstar : ∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ T.cells :=
          SquareEdgeDetails.hstarAt452 n w T hstarCoords z a b hpcoords hpstrict
      have hpnot : p ∉ BoundaryFootprintVertices T :=
        (P4456T2VertexInterior T hnonempty p hpFoot).2.mpr hstar
      rcases hpIsEnd with h | h
      · rw [← h] at hxB
        exact hpnot hxB
      · rw [← h] at hyB
        exact hpnot hyB
    · have hcoords : c = a ∧ d = b + 1 := SquareEdgeProof.hcoordsAt367 n w z v a b hza c d hvc
        hvform
      let pa : Nat := if 0 < a then a else a + 1
      let pb : Nat := b + 1
      let p : GaussianInt := if 0 < a then z + ⟨0,1⟩ else z + 1 + ⟨0,1⟩
      have hpcoords : p = w + (⟨(pa : Int), (pb : Int)⟩ : GaussianInt) :=
          SquareEdgeDetails.hpcoordsAt468 w z a b hza
      have hcoordsN : 1 < n := SquareEdgeDetails.hcoordsNAt471 n hn a b c d hd hcoords
      have hpstrict : 0 < pa ∧ pa < n ∧ 0 < pb ∧ pb < n := SquareEdgeDetails.hpstrictAt475 n a b
          ha c d hd hcoords hcoordsN
      have hpIsEnd : p = x ∨ p = y := SquareEdgeDetails.hpIsEndAt478 x y z a hor
      have hpFoot : p ∈ FootprintVertices T := SquareEdgeDetails.hpFootAt484 T x y z v hedgeInfo
          hz a hpIsEnd
      have hstar : ∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ T.cells :=
          SquareEdgeDetails.hstarAt491 n w T hstarCoords z a b hpcoords hpstrict
      have hpnot : p ∉ BoundaryFootprintVertices T :=
        (P4456T2VertexInterior T hnonempty p hpFoot).2.mpr hstar
      rcases hpIsEnd with h | h
      · rw [← h] at hxB
        exact hpnot hxB
      · rw [← h] at hyB
        exact hpnot hyB
  · intro x hx y hy hxy
    obtain ⟨a,b,ha,hb,hxcoord⟩ := hvertex_coords x hx
    obtain ⟨c,d,hc,hd,hycoord⟩ := hvertex_coords y hy
    change y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0,1⟩ ∨ y = x - ⟨0,1⟩ at hxy
    rcases hxy with h | h | h | h
    · have heq : w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) =
          (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) + 1 := SquareEdgeDetails.heqAt507 w x y a
              b hxcoord c d hycoord h
      have hcd : c = a + 1 ∧ d = b := SquareEdgeDetails.hcdAt513 n w a b c d heq
      have hset : ({x,y} : Finset GaussianInt) =
          {w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
            w + (⟨((a+1 : Nat) : Int), (b : Int)⟩ : GaussianInt)} := SquareEdgeDetails.hsetAt520
                w x y a b hxcoord c d hycoord hcd
      rw [hset]
      exact hEdgeH a b (by omega) (by omega)
    · have heq : w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) =
          (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt)) + 1 := SquareEdgeDetails.heqAt526 w x y a
              b hxcoord c d hycoord h
      have hcd : a = c + 1 ∧ b = d := SquareEdgeDetails.hcdAt532 n w a b c d heq
      have hset : ({x,y} : Finset GaussianInt) =
          {w + (⟨(c : Int), (d : Int)⟩ : GaussianInt),
            w + (⟨((c+1 : Nat) : Int), (d : Int)⟩ : GaussianInt)} := SquareEdgeDetails.hsetAt539
                n w x y a b hxcoord c d hycoord hcd
      rw [hset, Finset.pair_comm]
      simpa [Finset.pair_comm] using hEdgeH c d (by omega) (by omega)
    · have heq : w + (⟨(c : Int), (d : Int)⟩ : GaussianInt) =
          (w + (⟨(a : Int), (b : Int)⟩ : GaussianInt)) + ⟨0,1⟩ := SquareEdgeDetails.heqAt548 w x
              y a b hxcoord c d hycoord h
      have hcd : c = a ∧ d = b + 1 := SquareEdgeDetails.hcdAt554 n w a b c d heq
      have hset : ({x,y} : Finset GaussianInt) =
          {w + (⟨(a : Int), (b : Int)⟩ : GaussianInt),
            w + (⟨(a : Int), ((b+1 : Nat) : Int)⟩ : GaussianInt)} := SquareEdgeDetails.hsetAt561
                w x y a b hxcoord c d hycoord hcd
      rw [hset]
      exact hEdgeV a b (by omega) (by omega)
    · have heq : w + (⟨(a : Int), (b : Int)⟩ : GaussianInt) =
          (w + (⟨(c : Int), (d : Int)⟩ : GaussianInt)) + ⟨0,1⟩ := SquareEdgeDetails.heqAt567 w x
              y a b hxcoord c d hycoord h
      have hcd : a = c ∧ b = d + 1 := SquareEdgeDetails.hcdAt573 n w a b c d heq
      have hset : ({x,y} : Finset GaussianInt) =
          {w + (⟨(c : Int), (d : Int)⟩ : GaussianInt),
            w + (⟨(c : Int), ((d+1 : Nat) : Int)⟩ : GaussianInt)} := SquareEdgeDetails.hsetAt580
                n w x y a b hxcoord c d hycoord hcd
      rw [hset, Finset.pair_comm]
      simpa [Finset.pair_comm] using hEdgeV c d (by omega) (by omega)

end ApollonianSuperharmonic

end
