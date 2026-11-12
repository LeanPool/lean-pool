/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5352T2LiteralNormalization
public import LeanPool.ApollonianSuperharmonic.P5352T2VectorPlacements
public import LeanPool.ApollonianSuperharmonic.P5352T2RightFirst
public import LeanPool.ApollonianSuperharmonic.P5352T2RightSecond
public import LeanPool.ApollonianSuperharmonic.P5352T2RightHorizontal
public import LeanPool.ApollonianSuperharmonic.P5352T2FirstUnit
public import LeanPool.ApollonianSuperharmonic.P5352T2SecondUnit
public import LeanPool.ApollonianSuperharmonic.P5352T2Predecessor0
public import LeanPool.ApollonianSuperharmonic.P5352T2Predecessor1
public import LeanPool.ApollonianSuperharmonic.P5352T2Predecessor2
public import LeanPool.ApollonianSuperharmonic.P5352T2Predecessor3

-- [TABLET NODE: DiamondTerminalWebStencilLedger]

/-!
# DiamondTerminalWebStencilLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondTerminalWebStencilLedger (K : DiamondParameter) (hk : 1 < K.1) :
    let q := DiamondRecursiveQuadruple K
    (∀ (i : Fin 3) (e : Bool) (T T' : ProtoTile)
        (h h' : PartialOdometer) (p p' : ℝ × ℝ)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      TileOdometer (q 0) T h → TileOdometer (q 0) T' h' →
      PartialOdometerSlope h = some p →
      PartialOdometerSlope h' = some p' →
      TileCentroid T' - TileCentroid T =
        (if e = true then (1 : ℝ) else -1) •
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) →
      p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).re →
      p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).im →
      OdometerCompatibility h h' →
      GlobalOdometerExtends g h → GlobalOdometerExtends g h' →
      x ∈ h.domain → x ∈ h'.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ h'.domain) →
      ((∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
            s = x - 1 - ⟨0, 1⟩ → s ∈ T.cells ∨ s ∈ T'.cells) →
          FourNeighborLaplacian g x = 1) ∧
      (¬ (∀ s, s = x ∨ s = x - 1 ∨ s = x - ⟨0, 1⟩ ∨
            s = x - 1 - ⟨0, 1⟩ → s ∈ T.cells ∨ s ∈ T'.cells) →
          FourNeighborLaplacian g x = 0)) ∧
    ∀ (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer) (p₀ pᵢ : ℝ × ℝ)
        (g : IntegerLatticeFunction) (x : GaussianInt),
      TileOdometer (q 0) T₀ h₀ → TileOdometer (q i.succ) Tᵢ hᵢ →
      PartialOdometerSlope h₀ = some p₀ →
      PartialOdometerSlope hᵢ = some pᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
             BandVectors.1 (q 0) (q i.succ))) →
      pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).1 →
      pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).2 →
      OdometerCompatibility h₀ hᵢ →
      GlobalOdometerExtends g h₀ → GlobalOdometerExtends g hᵢ →
      x ∈ h₀.domain → x ∈ hᵢ.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₀.domain ∨ y ∈ hᵢ.domain) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let UR := TileTranslation T₀ uR
      (x ∈ FootprintVertices UR → FourNeighborLaplacian g x = 0) ∧
      (x ∉ FootprintVertices UR → FourNeighborLaplacian g x = 1) := by
-- BODY
  classical
  dsimp only
  have positive (i : Fin 3) (T U : ProtoTile)
      (h l : PartialOdometer) (p r : ℝ × ℝ)
      (g : IntegerLatticeFunction) (x : GaussianInt)
      (hT : TileOdometer ((DiamondRecursiveQuadruple K) 0) T h)
      (hU : TileOdometer ((DiamondRecursiveQuadruple K) 0) U l)
      (hp : PartialOdometerSlope h = some p)
      (hr : PartialOdometerSlope l = some r)
      (hc : TileCentroid U - TileCentroid T =
        GaussianRealPoint (BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
          ((DiamondRecursiveQuadruple K) i.succ)))
      (hsx : r.1-p.1 = (BandVectors.2 ((DiamondRecursiveQuadruple K) 0)
          ((DiamondRecursiveQuadruple K) i.succ)).re)
      (hsy : r.2-p.2 = (BandVectors.2 ((DiamondRecursiveQuadruple K) 0)
          ((DiamondRecursiveQuadruple K) i.succ)).im)
      (he : GlobalOdometerExtends g h) (he' : GlobalOdometerExtends g l)
      (hx : x ∈ h.domain) (hx' : x ∈ l.domain)
      (hcover : ∀ y, y=x ∨ y=x+1 ∨ y=x-1 ∨
        y=x+⟨0,1⟩ ∨ y=x-⟨0,1⟩ → y∈h.domain ∨ y∈l.domain) :
      ((∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
        y∈T.cells ∨ y∈U.cells) → FourNeighborLaplacian g x=1) ∧
      (¬ (∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
        y∈T.cells ∨ y∈U.cells) → FourNeighborLaplacian g x=0) := by
    obtain ⟨w,d,a,B,f,hd,hd',hcell,hcell',hfoot,hcent,hs,hs',hv,hv',hlap⟩ :=
      P5352T2LiteralNormalization K hk 0 T U h l p r g hT hU hp hr he he'
    obtain ⟨hvec,hsl,_⟩ := P5352T2VectorPlacements K hk i 0
    rw [hvec] at hc
    rw [hsl] at hsx hsy
    have deq : d = (P5352T2PlacementData K.1 i).1.1 := by
      have h := hcent.symm.trans hc
      simp only [sub_self, zero_add] at h
      apply Zsqrtd.ext
      · have e := congrArg Prod.fst h
        change (d.re : ℝ) = ((P5352T2PlacementData K.1 i).1.1.re : ℝ) at e
        exact_mod_cast e
      · have e := congrArg Prod.snd h
        change (d.im : ℝ) = ((P5352T2PlacementData K.1 i).1.1.im : ℝ) at e
        exact_mod_cast e
    have aeq : a = (P5352T2PlacementData K.1 i).1.2 := by
      simp only [sub_self, zero_add] at hs hs'
      apply Zsqrtd.ext
      · exact_mod_cast hs.symm.trans hsx
      · exact_mod_cast hs'.symm.trans hsy
    subst d
    subst a
    have cover : ∀ y, y=x-w ∨ y=x-w+1 ∨ y=x-w-1 ∨
        y=x-w+⟨0,1⟩ ∨ y=x-w-⟨0,1⟩ →
        y ∈ FootprintVertices (P5352T2Sources K hk 0).1 ∨
        y-(P5352T2PlacementData K.1 i).1.1 ∈
          FootprintVertices (P5352T2Sources K hk 0).1 := by
      intro y hy
      have hh := hcover (y+w) (by
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
      rcases hh with hh | hh
      · exact Or.inl (by simpa only [add_sub_cancel_right] using (hd _).mp hh)
      · exact Or.inr (by simpa only [add_sub_cancel_right] using (hd' _).mp hh)
    have cells :
        (∀ y, y=x-w ∨ y=x-w-1 ∨ y=x-w-⟨0,1⟩ ∨ y=x-w-1-⟨0,1⟩ →
          y ∈ (P5352T2Sources K hk 0).1.cells ∨
          y-(P5352T2PlacementData K.1 i).1.1 ∈ (P5352T2Sources K hk 0).1.cells) ↔
        (∀ y, y=x ∨ y=x-1 ∨ y=x-⟨0,1⟩ ∨ y=x-1-⟨0,1⟩ →
          y∈T.cells ∨ y∈U.cells) := by
      constructor
      · intro H y hy
        have hh := H (y-w) (by
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
        exact hh.imp ((hcell y).mpr) ((hcell' y).mpr)
      · intro H y hy
        have hh := H (y+w) (by
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
        rcases hh with hh | hh
        · exact Or.inl (by simpa only [add_sub_cancel_right] using (hcell _).mp hh)
        · exact Or.inr (by simpa only [add_sub_cancel_right] using (hcell' _).mp hh)
    have hcase :
        ((∀ y, y=x-w ∨ y=x-w-1 ∨ y=x-w-⟨0,1⟩ ∨ y=x-w-1-⟨0,1⟩ →
          y ∈ (P5352T2Sources K hk 0).1.cells ∨
          y-(P5352T2PlacementData K.1 i).1.1 ∈ (P5352T2Sources K hk 0).1.cells) →
          FourNeighborLaplacian f (x-w)=1) ∧
        (¬ (∀ y, y=x-w ∨ y=x-w-1 ∨ y=x-w-⟨0,1⟩ ∨ y=x-w-1-⟨0,1⟩ →
          y ∈ (P5352T2Sources K hk 0).1.cells ∨
          y-(P5352T2PlacementData K.1 i).1.1 ∈ (P5352T2Sources K hk 0).1.cells) →
          FourNeighborLaplacian f (x-w)=0) := by
      fin_cases i
      · exact P5352T2RightFirst K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
      · exact P5352T2RightSecond K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
      · exact P5352T2RightHorizontal K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
    rw [hlap x]
    exact ⟨fun H => hcase.1 (cells.mpr H), fun H => hcase.2 (fun h => H (cells.mp h))⟩
  constructor
  · intro i e T U h l p r g x hT hU hp hr hc hsx hsy _ he he' hx hx' hcover
    cases e
    · have hc' : TileCentroid T - TileCentroid U =
          GaussianRealPoint (BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
            ((DiamondRecursiveQuadruple K) i.succ)) := by
        have hh := congrArg Neg.neg hc
        simpa using hh
      have hsx' : p.1-r.1 = (BandVectors.2 ((DiamondRecursiveQuadruple K) 0)
            ((DiamondRecursiveQuadruple K) i.succ)).re := by
        simp only [Bool.false_eq_true, ite_false, neg_one_mul] at hsx
        linarith
      have hsy' : p.2-r.2 = (BandVectors.2 ((DiamondRecursiveQuadruple K) 0)
            ((DiamondRecursiveQuadruple K) i.succ)).im := by
        simp only [Bool.false_eq_true, ite_false, neg_one_mul] at hsy
        linarith
      have H := positive i U T l h r p g x hU hT hr hp hc' hsx' hsy'
        he' he hx' hx (fun y hy => (hcover y hy).symm)
      simpa only [or_comm] using H
    · apply positive i T U h l p r g x hT hU hp hr
      · simpa using hc
      · simpa using hsx
      · simpa using hsy
      · exact he
      · exact he'
      · exact hx
      · exact hx'
      · exact hcover
  · intro i s T U h l p r g x hT hU hp hr hc hsx hsy _ he he' hx hx' hcover
    obtain ⟨w,d,a,B,f,hd,hd',hcell,hcell',hfoot,hcent,hs,hs',hv,hv',hlap⟩ :=
      P5352T2LiteralNormalization K hk i.succ T U h l p r g hT hU hp hr he he'
    obtain ⟨_,_,hvect,hslt,hright⟩ := P5352T2VectorPlacements K hk i s
    have deq : d = ((P5352T2PlacementData K.1 i).2 s).1 := by
      have hh := hcent.symm.trans (hc.trans hvect)
      apply Zsqrtd.ext
      · have e := congrArg Prod.fst hh
        dsimp at e
        exact_mod_cast (show (d.re : ℝ) =
          (((P5352T2PlacementData K.1 i).2 s).1.re : ℝ) by linarith only [e])
      · have e := congrArg Prod.snd hh
        dsimp at e
        exact_mod_cast (show (d.im : ℝ) =
          (((P5352T2PlacementData K.1 i).2 s).1.im : ℝ) by linarith only [e])
    have aeq : a = ((P5352T2PlacementData K.1 i).2 s).2.1 := by
      have ex := congrArg Prod.fst hslt
      have ey := congrArg Prod.snd hslt
      dsimp only at ex ey
      rw [ex] at hsx
      rw [ey] at hsy
      apply Zsqrtd.ext
      · exact_mod_cast (show (a.re : ℝ) =
          (((P5352T2PlacementData K.1 i).2 s).2.1.re : ℝ) by linarith only [hs, hsx])
      · exact_mod_cast (show (a.im : ℝ) =
          (((P5352T2PlacementData K.1 i).2 s).2.1.im : ℝ) by linarith only [hs', hsy])
    subst d
    subst a
    have cover : ∀ y, y=x-w ∨ y=x-w+1 ∨ y=x-w-1 ∨
        y=x-w+⟨0,1⟩ ∨ y=x-w-⟨0,1⟩ →
        y ∈ FootprintVertices (P5352T2Sources K hk 0).1 ∨
        y-((P5352T2PlacementData K.1 i).2 s).1 ∈
          FootprintVertices (P5352T2Sources K hk i.succ).1 := by
      intro y hy
      have hh := hcover (y+w) (by
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
      rcases hh with hh | hh
      · exact Or.inl (by simpa only [add_sub_cancel_right] using (hd _).mp hh)
      · exact Or.inr (by simpa only [add_sub_cancel_right] using (hd' _).mp hh)
    have hcase :
        (x-w-((P5352T2PlacementData K.1 i).2 s).2.2 ∈
          FootprintVertices (P5352T2Sources K hk 0).1 →
          FourNeighborLaplacian f (x-w)=0) ∧
        (x-w-((P5352T2PlacementData K.1 i).2 s).2.2 ∉
          FootprintVertices (P5352T2Sources K hk 0).1 →
          FourNeighborLaplacian f (x-w)=1) := by
      fin_cases i
      · exact P5352T2FirstUnit K hk s f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
      · exact P5352T2SecondUnit K hk s f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
      · fin_cases s
        · exact P5352T2Predecessor0 K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
        · exact P5352T2Predecessor1 K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
        · exact P5352T2Predecessor2 K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
        · exact P5352T2Predecessor3 K hk f B (x-w) hv hv' ((hd x).mp hx) ((hd' x).mp hx') cover
    rw [hright, hfoot x, hlap x]
    exact hcase

end ApollonianSuperharmonic

end
