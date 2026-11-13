/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows
public import LeanPool.ApollonianSuperharmonic.P5537T1ScaledDiamondFormula
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources

-- [TABLET NODE: P5537T1UnitParentBoundary]

/-!
# P5537T1UnitParentBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5537T1UnitParentBoundary (K : DiamondParameter) (hk : 1 < K.1) :
    let A := P5352T2Sources K hk 0
    ∀ (i : Fin 3), i.val < 2 → ∀ (s : Fin 4),
      let D := P5352T2Sources K hk i.succ
      let M := (P5352T2PlacementData K.1 i).2 s
      ∃ b : Int, ∀ x : GaussianInt,
        x ∈ FootprintVertices A.1 → x-M.1 ∈ FootprintVertices D.1 →
        D.2.1 (x-M.1) + M.2.1.re*x.re + M.2.1.im*x.im - A.2.1 x = b := by
-- BODY
  dsimp only
  have unitMem (z : GaussianInt) :
      z ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) ↔
        0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 := by
    simp only [FootprintVertices, Finset.singleton_nonempty, ↓reduceIte,
      Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left]
    simp only [zero_add, Zsqrtd.ext_iff, Zsqrtd.re_zero, Zsqrtd.im_zero,
      Zsqrtd.re_one, Zsqrtd.im_one, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  have hF (z : GaussianInt) (hz : z ∈ FootprintVertices (DiamondTile K.1)) :
      DiamondOdometer K z = P4207T1DiamondFormula z :=
    (P5352T2DomainRows K z).2 hz
  have scale (z : GaussianInt) :
      4 * P4207T1DiamondFormula z =
        2*z.re^2-2*|z.re|-(z.re-z.im)^2+(z.re-z.im)%2 := by
    exact P5537T1ScaledDiamondFormula.1 z.re z.im
  have ht := P5537T1ScaledDiamondFormula.2 (K.1 : Int)
  have ht' := P5537T1ScaledDiamondFormula.2 ((K.1 : Int)+1)
  rw [show (K.1:Int)+1-1 = (K.1:Int) by ring] at ht'
  rw [mul_comm ((K.1:Int)+1) (K.1:Int)] at ht'
  intro i hi s
  fin_cases i
  · fin_cases s
    · refine ⟨-(K.1:Int)^2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨0,2*(K.1:Int)⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hy : x.im = 2*(K.1:Int) := by omega
      have hx01 : x.re = 0 ∨ x.re = 1 := by omega
      change (CurvatureOneOdometer ⟨0,1⟩).value (x-⟨0,2*(K.1:Int)⟩) +
        (K.1:Int)*x.re + (-(K.1:Int))*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hx01 with hxr | hxr
      all_goals
        simp only [hxr, hy] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.ext_iff, Zsqrtd.re_sub,
          Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one, hxr, hy]
        norm_num at hs ⊢
        have hm : (-(2*(K.1:Int)))%2 = 0 := by omega
        have hm' : (1-2*(K.1:Int))%2 = 1 := by omega
        try
        nlinarith only [hs]
    · refine ⟨-((K.1:Int)*((K.1:Int)+1)/2), ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-(K.1:Int)-1,(K.1:Int)⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hxr : x.re = -(K.1:Int) := by omega
      have hy01 : x.im = (K.1:Int) ∨ x.im = (K.1:Int)+1 := by omega
      change (CurvatureOneOdometer ⟨0,1⟩).value (x-⟨-(K.1:Int)-1,(K.1:Int)⟩) +
        0*x.re + (-(K.1:Int)-1)*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hy01 with hy | hy
      all_goals
        simp only [hxr, hy, abs_neg, abs_of_nonneg (by omega : 0 ≤ (K.1:Int))] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.ext_iff, Zsqrtd.re_sub,
          Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one, hxr, hy]
        norm_num at hs ⊢
        have hm : (-(K.1:Int)-(K.1:Int))%2 = 0 := by omega
        have hm' : (-(K.1:Int)-((K.1:Int)+1))%2 = 1 := by omega
        try simp only [hm, hm'] at hs
        nlinarith only [hs, ht']
    · refine ⟨1, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-1,-1⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hy : x.im = 0 := by omega
      have hx01 : x.re = -1 ∨ x.re = 0 := by omega
      change (CurvatureOneOdometer ⟨0,1⟩).value (x-⟨-1,-1⟩) +
        (-1)*x.re + (-1)*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hx01 with hxr | hxr
      all_goals
        simp only [hxr, hy] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.ext_iff, Zsqrtd.re_sub,
          Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one, hxr, hy]
        norm_num at hs ⊢
        nlinarith only [hs]
    · refine ⟨(K.1:Int)*((K.1:Int)-1)/2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨(K.1:Int),(K.1:Int)-1⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hxr : x.re = (K.1:Int) := by omega
      have hy01 : x.im = (K.1:Int)-1 ∨ x.im = (K.1:Int) := by omega
      change (CurvatureOneOdometer ⟨0,1⟩).value (x-⟨(K.1:Int),(K.1:Int)-1⟩) +
        ((K.1:Int)-1)*x.re + 0*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hy01 with hy | hy
      all_goals
        simp only [hxr, hy, abs_of_nonneg (by omega : 0 ≤ (K.1:Int))] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.ext_iff, Zsqrtd.re_sub,
          Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one,
          Zsqrtd.im_one, hxr, hy]
        norm_num at hs ⊢
        nlinarith only [hs, ht]
  · fin_cases s
    · refine ⟨-((K.1:Int)*((K.1:Int)-1)/2), ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-(K.1:Int)-1,(K.1:Int)-1⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hxr : x.re = -(K.1:Int) := by omega
      have hy01 : x.im = (K.1:Int)-1 ∨ x.im = (K.1:Int) := by omega
      change (CurvatureOneOdometer 0).value (x-⟨-(K.1:Int)-1,(K.1:Int)-1⟩) +
        0*x.re + (-(K.1:Int))*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hy01 with hy | hy
      all_goals
        simp only [hxr, hy, abs_neg, abs_of_nonneg (by omega : 0 ≤ (K.1:Int))] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.im_zero, ite_self]
        norm_num at hs ⊢
        have hm : (-(K.1:Int)-(K.1:Int))%2 = 0 := by omega
        have hm' : (-(K.1:Int)-((K.1:Int)-1))%2 = 1 := by omega
        try simp only [hm, hm'] at hs
        nlinarith only [hs, ht]
    · refine ⟨0, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨0,-1⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hy : x.im = 0 := by omega
      have hx01 : x.re = 0 ∨ x.re = 1 := by omega
      change (CurvatureOneOdometer 0).value (x-⟨0,-1⟩) +
        0*x.re + 0*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hx01 with hxr | hxr
      all_goals
        simp only [hxr, hy] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.im_zero, ite_self]
        norm_num at hs ⊢
        nlinarith only [hs]
    · refine ⟨(K.1:Int)*((K.1:Int)+1)/2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨(K.1:Int),(K.1:Int)⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hxr : x.re = (K.1:Int) := by omega
      have hy01 : x.im = (K.1:Int) ∨ x.im = (K.1:Int)+1 := by omega
      change (CurvatureOneOdometer 0).value (x-⟨(K.1:Int),(K.1:Int)⟩) +
        (K.1:Int)*x.re + 0*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hy01 with hy | hy
      all_goals
        simp only [hxr, hy, abs_of_nonneg (by omega : 0 ≤ (K.1:Int))] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.im_zero, ite_self]
        norm_num at hs ⊢
        nlinarith only [hs, ht']
    · refine ⟨-(K.1:Int)^2, ?_⟩
      intro x hx hd
      change x ∈ FootprintVertices (DiamondTile K.1) at hx
      change x-⟨-1,2*(K.1:Int)⟩ ∈ FootprintVertices (⟨{0},0⟩ : ProtoTile) at hd
      have hc := (P5352T2DomainRows K x).1.mp hx
      have hu := (unitMem _).mp hd
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hu
      have hy : x.im = 2*(K.1:Int) := by omega
      have hx01 : x.re = -1 ∨ x.re = 0 := by omega
      change (CurvatureOneOdometer 0).value (x-⟨-1,2*(K.1:Int)⟩) +
        (K.1:Int)*x.re + (-(K.1:Int))*x.im - DiamondOdometer K x = _
      rw [hF x hx]
      have hs := scale x
      rcases hx01 with hxr | hxr
      all_goals
        simp only [hxr, hy] at hs ⊢
        simp only [CurvatureOneOdometer, Zsqrtd.im_zero, ite_self]
        norm_num at hs ⊢
        have hm : (-(2*(K.1:Int)))%2 = 0 := by omega
        have hm' : (-1-2*(K.1:Int))%2 = 1 := by omega
        try
        nlinarith only [hs]
  · change (2 : Nat) < 2 at hi
    omega

end ApollonianSuperharmonic

end
