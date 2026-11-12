/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FinitePolyominoDiskCriterion
public import
    LeanPool.ApollonianSuperharmonic.P5617T1RectangleReachabilityAndBasepointConnectivity
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5116T1PredecessorDeletionDisk]

/-!
# P5116T1PredecessorDeletionDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5116T1PredecessorDeletionDisk (k : Nat) (hk : 1 < k)
    (shifted : Bool) (T : ProtoTile)
    (hcells : T.cells = (DiamondTile k).cells \
      (if shifted then TileTranslation (DiamondTile (k - 1)) ⟨0, 2⟩
        else DiamondTile (k - 1)).cells) :
    LatticeTile T := by
-- BODY
  classical
  let reach (A : Set LatticeCell) := Relation.ReflTransGen
    (fun x y => FourNeighborAdjacent x y ∧ x ∈ A ∧ y ∈ A)
  have single (A : Set LatticeCell) {x y : LatticeCell}
      (hx : x ∈ A) (hy : y ∈ A) (hxy : FourNeighborAdjacent x y) :
      reach A x y := Relation.ReflTransGen.single ⟨hxy, hx, hy⟩
  obtain ⟨rect, connected⟩ := P5617T1RectangleReachabilityAndBasepointConnectivity
  have diamond (m : Nat) (z : LatticeCell) : z ∈ (DiamondTile m).cells ↔
      0 ≤ z.im ∧ z.im < 2 * (m : Int) ∧
      -(z.im + 1) ≤ z.re ∧ z.re < z.im + 1 ∧
      -(2 * (m : Int) - z.im) ≤ z.re ∧ z.re < 2 * (m : Int) - z.im :=
    (P4194T1DiamondCellRows m z).1
  let B : Set LatticeCell :=
    {z | z ∈ (DiamondTile k).cells ∧ z ∉ (DiamondTile (k - 1)).cells}
  have bmem (z : LatticeCell) : z ∈ B ↔
      z ∈ (DiamondTile k).cells ∧ z ∉ (DiamondTile (k - 1)).cells := Iff.rfl
  let o : LatticeCell := ⟨0, 2 * (k : Int) - 2⟩
  have ho : o ∈ B := by
    simp only [bmem, diamond]
    norm_num [o]
    omega
  have climb : ∀ h : Int, ∀ p : LatticeCell, p.im = h → p ∈ B → reach B p o := by
    intro h
    induction h using Int.inductionOn' (b := 2 * (k : Int) - 2) with
    | zero =>
      intro p hpi hp
      apply rect B p o
      intro z h1 h2 h3 h4
      simp only [bmem, diamond] at hp ⊢
      dsimp [o] at h1 h2 h3 h4
      omega
    | succ h hh ih =>
      intro p hpi hp
      apply rect B p o
      intro z h1 h2 h3 h4
      simp only [bmem, diamond] at hp ⊢
      dsimp [o] at h1 h2 h3 h4
      omega
    | pred h hh ih =>
      intro p hpi hp
      let a : Int := if p.re < 0 then p.im - 2 * (k : Int) + 1
        else 2 * (k : Int) - p.im - 2
      let m : LatticeCell := ⟨a, p.im⟩
      let n : LatticeCell := ⟨a, h⟩
      have hm : m ∈ B := by
        simp only [bmem, diamond] at hp ⊢
        dsimp [m, a]
        split_ifs <;> omega
      have hn : n ∈ B := by
        simp only [bmem, diamond] at hp ⊢
        dsimp [n, a]
        split_ifs <;> omega
      have hr : reach B p m := by
        apply rect B p m
        intro z h1 h2 h3 h4
        simp only [bmem, diamond] at hp ⊢
        dsimp [m, a] at h1 h2 h3 h4
        split_ifs at * <;> omega
      exact hr.trans ((single B hm hn (by
        apply Or.inr; apply Or.inr; apply Or.inl
        apply Zsqrtd.ext <;> dsimp [n, m] <;> omega)).trans (ih n rfl hn))
  let e : LatticeCell := ⟨(k : Int) + 1, -1⟩
  have exterior (p : LatticeCell) (hp : p ∉ (DiamondTile k).cells) :
      reach Bᶜ p e := by
    let a : Int := if p.re < 0 then -(k : Int) - 1 else (k : Int) + 1
    let m : LatticeCell := ⟨a, p.im⟩
    let n : LatticeCell := ⟨a, -1⟩
    apply (rect Bᶜ p m ?_).trans ((rect Bᶜ m n ?_).trans (rect Bᶜ n e ?_))
    all_goals
      intro z h1 h2 h3 h4
      change z ∉ B
      rw [bmem, diamond]
      rw [diamond] at hp
      dsimp [m, n, e, a] at h1 h2 h3 h4
      split_ifs at * <;> omega
  have he : e ∈ Bᶜ := by
    change e ∉ B
    simp only [bmem, diamond]
    norm_num [e]
  have escape (p : LatticeCell) (hp : p ∈ Bᶜ) : reach Bᶜ p e := by
    by_cases hpD : p ∈ (DiamondTile k).cells
    · have hpP : p ∈ (DiamondTile (k - 1)).cells := by
        change p ∉ B at hp
        rw [bmem] at hp
        tauto
      let m : LatticeCell := ⟨0, p.im⟩
      let n : LatticeCell := ⟨0, -1⟩
      apply (rect Bᶜ p m ?_).trans
        ((rect Bᶜ m n ?_).trans (exterior n (by rw [diamond]; norm_num [n])))
      all_goals
        intro z h1 h2 h3 h4
        change z ∉ B
        simp only [bmem, diamond]
        rw [diamond] at hpP
        dsimp [m, n] at h1 h2 h3 h4
        omega
    · exact exterior p hpD
  let A : Set LatticeCell := T.cells
  let f : LatticeCell → LatticeCell := fun z =>
    ⟨z.re, if shifted then 2 * (k : Int) - 1 - z.im else z.im⟩
  have invol (z : LatticeCell) : f (f z) = z := by
    apply Zsqrtd.ext <;> cases shifted <;> simp [f]
  have adj (p q : LatticeCell) (hpq : FourNeighborAdjacent p q) :
      FourNeighborAdjacent (f p) (f q) := by
    rcases hpq with h | h | h | h <;> subst q <;> cases shifted <;>
      simp [FourNeighborAdjacent, f, Zsqrtd.ext_iff] <;> omega
  have translated_mem (z : GaussianInt) :
      z ∈ (TileTranslation (DiamondTile (k - 1)) ⟨0, 2⟩).cells ↔
        z - ⟨0, 2⟩ ∈ (DiamondTile (k - 1)).cells := by
    change z ∈ (DiamondTile (k - 1)).cells.image (GaussianTranslation ⟨0, 2⟩) ↔ _
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hy
    · intro hz
      exact Finset.mem_image.mpr ⟨z - ⟨0, 2⟩, hz, by simp [GaussianTranslation]⟩
  have amem (z : LatticeCell) : z ∈ A ↔ f z ∈ B := by
    change z ∈ T.cells ↔ _
    rw [hcells, Finset.mem_sdiff]
    cases shifted <;> simp only [Bool.false_eq_true, ↓reduceIte,
      translated_mem, bmem, diamond] <;>
      norm_num [f]; omega
  have mapped (U V : Set LatticeCell)
      (hm : ∀ z ∈ U, f z ∈ V) {p q : LatticeCell} (hpq : reach U p q) :
      reach V (f p) (f q) := by
    induction hpq with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
      exact ih.trans (single V (hm _ hstep.2.1) (hm _ hstep.2.2)
        (adj _ _ hstep.1))
  have intoA (z : LatticeCell) (hz : z ∈ B) : f z ∈ A := by
    rw [amem, invol]
    exact hz
  have intoAc (z : LatticeCell) (hz : z ∈ Bᶜ) : f z ∈ Aᶜ := by
    change f z ∉ A
    rw [amem, invol]
    exact hz
  have inside : FourNeighborConnected A := by
    apply connected A (f o) (intoA o ho)
    intro p hp
    have h := mapped B A intoA (climb (f p).im (f p) rfl ((amem p).mp hp))
    simpa only [invol] using h
  have outside : FourNeighborConnected Aᶜ := by
    apply connected Aᶜ (f e) (intoAc e he)
    intro p hp
    have hfp : f p ∈ Bᶜ := by
      change f p ∉ B
      exact fun h => hp ((amem p).mpr h)
    have h := mapped Bᶜ Aᶜ intoAc (escape (f p) hfp)
    simpa only [invol] using h
  have checker : NoCheckerboardCellVertex A := by
    intro z
    simp only [amem, bmem, diamond]
    cases shifted <;>
      norm_num [f, Zsqrtd.re_sub, Zsqrtd.im_sub] <;> omega
  exact FinitePolyominoDiskCriterion T inside outside checker

end ApollonianSuperharmonic

end
