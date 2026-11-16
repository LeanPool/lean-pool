/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4207T1FormulaRestriction
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas

-- [TABLET NODE: P4207T1ShiftedPredecessor]

/-!
# P4207T1ShiftedPredecessor

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4207T1ShiftedPredecessor (n : Nat) :
    P4207T1FormulaRestriction (TileTranslation (DiamondTile n) ⟨0, 2⟩) =
      PartialOdometerAffineTranslate
        (P4207T1FormulaRestriction (DiamondTile n)) ⟨0, 2⟩ ⟨1, -1⟩ 1 := by
-- BODY
  classical
  let h := P4207T1FormulaRestriction (DiamondTile n)
  let k := P4207T1FormulaRestriction (TileTranslation (DiamondTile n) ⟨0, 2⟩)
  let l := PartialOdometerAffineTranslate h ⟨0, 2⟩ ⟨1, -1⟩ 1
  have dom (T : ProtoTile) (x : GaussianInt) :
      x ∈ (P4207T1FormulaRestriction T).domain ↔ x ∈ FootprintVertices T := by
    change x ∈ ((P4207T1FormulaRestriction T).domain : Set GaussianInt) ↔ _
    by_cases h : T.cells.Nonempty <;>
      simp [P4207T1FormulaRestriction, FootprintVertices, h]
  have value (T : ProtoTile) (x : GaussianInt)
      (hx : x ∈ (P4207T1FormulaRestriction T).domain) :
      (P4207T1FormulaRestriction T).value x = P4207T1DiamondFormula x := by
    change (if x ∈ (P4207T1FormulaRestriction T).domain then _ else 0) = _
    exact ite_eq_left hx
  have member (x : GaussianInt) : x ∈ k.domain ↔ x - ⟨0, 2⟩ ∈ h.domain := by
    dsimp [k, h]
    rw [dom, dom, (TileTranslationFormulas (DiamondTile n) ⟨0, 2⟩).2.2.2.2.2.1]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [GaussianTranslation] using hy
    · intro hx
      exact ⟨x - ⟨0, 2⟩, hx, by simp [GaussianTranslation]⟩
  have hd : k.domain = l.domain := by
    ext x
    exact (member x).trans ((PartialOdometerAffineTranslateFormulas h
      ⟨0, 2⟩ ⟨1, -1⟩ 1).2.1 x).symm
  have hv : k.value = l.value := by
    funext x
    by_cases hx : x ∈ k.domain
    · have hl : x ∈ l.domain := hd ▸ hx
      have hp := (member x).mp hx
      rw [value _ x hx]
      rw [(PartialOdometerAffineTranslateFormulas h ⟨0, 2⟩ ⟨1, -1⟩ 1).2.2.1 x hl]
      rw [value _ (x - ⟨0, 2⟩) hp]
      have shift := P4207T1FloorArithmetic.2.2.1 (x - ⟨0, 2⟩)
      simp only [sub_add_cancel, Zsqrtd.re_sub, Zsqrtd.im_sub] at shift
      dsimp at shift ⊢
      omega
    · have hl : x ∉ l.domain := by simpa [← hd] using hx
      rw [k.value_outside x hx, l.value_outside x hl]
  have extensional (a b : PartialOdometer) (hd : a.domain = b.domain)
      (hv : a.value = b.value) : a = b := by
    cases a
    cases b
    simp only at hd hv
    cases hd
    cases hv
    rfl
  exact extensional k l hd hv

end ApollonianSuperharmonic

end
