/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5537T1UnitParentBoundary
public import LeanPool.ApollonianSuperharmonic.P5537T1PredecessorCoordinates
public import LeanPool.ApollonianSuperharmonic.P5537T1PredecessorValues

-- [TABLET NODE: P5491T1DiamondParentBoundary]

/-!
# P5491T1DiamondParentBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1DiamondParentBoundary (K : DiamondParameter) (hk : 1 < K.1)
    (i : Fin 3) (s : Fin 4) :
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk i.succ
    let M := (P5352T2PlacementData K.1 i).2 s
    ∃ b : ℤ, ∀ x : GaussianInt,
      x ∈ FootprintVertices A.1 → x-M.1 ∈ FootprintVertices D.1 →
      D.2.1 (x-M.1) + M.2.1.re*x.re + M.2.1.im*x.im - A.2.1 x = b := by
-- BODY
  dsimp only
  by_cases hi : i.val < 2
  · exact P5537T1UnitParentBoundary K hk i hi s
  · have hi2 : i = 2 := by apply Fin.ext; omega
    subst i
    have hn : 2 ≤ (K.1 : Int) := by exact_mod_cast hk
    let L : DiamondParameter := ⟨K.1-1, by omega⟩
    have value (M : DiamondParameter) (z : GaussianInt)
        (hz : z ∈ FootprintVertices (DiamondTile M.1)) :
        DiamondOdometer M z = P4207T1DiamondFormula z :=
      (P5352T2DomainRows M z).2 hz
    fin_cases s
    · refine ⟨-((K.1:Int)*((K.1:Int)-1)/2), ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨(K.1:Int),1-(K.1:Int)⟩ ∈
        FootprintVertices (DiamondTile (K.1-1)) at hd
      have hc := (P5537T1PredecessorCoordinates K hk x).1.mp ⟨hx,hd⟩
      change DiamondOdometer L (x-⟨(K.1:Int),1-(K.1:Int)⟩) +
        0*x.re + ((K.1:Int)-1)*x.im - DiamondOdometer K x = _
      rw [value L _ hd, value K x hx]
      simpa only [P4207T1DiamondFormula, Zsqrtd.re_sub, Zsqrtd.im_sub,
        zero_mul, add_zero] using
        (P5537T1PredecessorValues (K.1:Int) x.re x.im hn).1 hc
    · refine ⟨(K.1:Int)*((K.1:Int)+1)/2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨(K.1:Int),(K.1:Int)+1⟩ ∈
        FootprintVertices (DiamondTile (K.1-1)) at hd
      have hc := (P5537T1PredecessorCoordinates K hk x).2.1.mp ⟨hx,hd⟩
      change DiamondOdometer L (x-⟨(K.1:Int),(K.1:Int)+1⟩) +
        (K.1:Int)*x.re + 0*x.im - DiamondOdometer K x = _
      rw [value L _ hd, value K x hx]
      simpa only [P4207T1DiamondFormula, Zsqrtd.re_sub, Zsqrtd.im_sub,
        zero_mul, add_zero] using
        (P5537T1PredecessorValues (K.1:Int) x.re x.im hn).2.1 hc
    · refine ⟨-((K.1:Int)*((K.1:Int)+1)/2), ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-(K.1:Int),(K.1:Int)+1⟩ ∈
        FootprintVertices (DiamondTile (K.1-1)) at hd
      have hc := (P5537T1PredecessorCoordinates K hk x).2.2.1.mp ⟨hx,hd⟩
      change DiamondOdometer L (x-⟨-(K.1:Int),(K.1:Int)+1⟩) +
        1*x.re + (-(K.1:Int))*x.im - DiamondOdometer K x = _
      rw [value L _ hd, value K x hx]
      simpa only [P4207T1DiamondFormula, Zsqrtd.re_sub, Zsqrtd.im_sub,
        Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg, Zsqrtd.im_neg,
        sub_neg_eq_add, one_mul, neg_mul, sub_eq_add_neg, neg_neg] using
        (P5537T1PredecessorValues (K.1:Int) x.re x.im hn).2.2.1 hc
    · refine ⟨(K.1:Int)*((K.1:Int)-1)/2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-(K.1:Int),1-(K.1:Int)⟩ ∈
        FootprintVertices (DiamondTile (K.1-1)) at hd
      have hc := (P5537T1PredecessorCoordinates K hk x).2.2.2.mp ⟨hx,hd⟩
      change DiamondOdometer L (x-⟨-(K.1:Int),1-(K.1:Int)⟩) +
        (1-(K.1:Int))*x.re + (-1)*x.im - DiamondOdometer K x = _
      rw [value L _ hd, value K x hx]
      simpa only [P4207T1DiamondFormula, Zsqrtd.re_sub, Zsqrtd.im_sub,
        Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg, Zsqrtd.im_neg,
        sub_neg_eq_add, neg_one_mul, sub_eq_add_neg, neg_neg] using
        (P5537T1PredecessorValues (K.1:Int) x.re x.im hn).2.2.2 hc

end ApollonianSuperharmonic

end
