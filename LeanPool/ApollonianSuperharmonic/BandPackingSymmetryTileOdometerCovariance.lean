/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCurvature
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryDomainTransport

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhaseUnique
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPrototileFootprintSlopeCovariance
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: BandPackingSymmetryTileOdometerCovariance]

/-!
# BandPackingSymmetryTileOdometerCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TileOdometerSymmetryProof

private theorem odoPositiveCurvature :
    (by
      classical
      exact
        ∀ (D : CircleCoordinates), ∀ (V : ProtoTile), ∀ (k : PartialOdometer), TileOdometer D V k
            → V.cells.Nonempty → 0 < D.1 ) := by
  classical
  intro D V k ho hne
  induction ho with
  | line w x hw k hdom => simp at hne
  | unit z x V k hV hdom htrans => norm_num
  | decompose hq hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope =>
      exact (ProperBandCurvatureStructure _ hq).1

private theorem slopeCov :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), (∀ (D : CircleCoordinates), ∀ (V : ProtoTile), ∀ (k :
            PartialOdometer), TileOdometer D V k → V.cells.Nonempty → 0 < D.1) → (∀ (D :
            CircleCoordinates), ∀ (V : ProtoTile), ∀ (k : PartialOdometer), TileOdometer D V k →
            V.cells.Nonempty → PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g
            k) = (PartialOdometerSlope k).map (BandPackingSymmetrySlopeAction g V)) ) := by
  classical
  intro g odoPositiveCurvature D V k ho hne
  have hproto := TileOdometerBandPrototile D V k ho
  have hcurv := odoPositiveCurvature D V k ho hne
  have hdom := PositiveCurvatureTileOdometerDomain D V k hcurv ho
  exact BandPrototileFootprintSlopeCovariance g D V k hproto hne hdom

private theorem lineCircle :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (w : GaussianInt), (w = 1 ∨ w = -1) → ∃ w', (w' = 1 ∨ w' =
            -1) ∧ BandPackingSymmetryCircleAction a (0, w) = (0, w') ) := by
  classical
  intro a
  induction a with
  | identity => intro w hw; exact ⟨w, hw, rfl⟩
  | negate =>
      intro w hw
      refine ⟨-w, ?_, ?_⟩
      · rcases hw with h | h <;> subst w <;> norm_num
      · rfl
  | conjugate =>
      intro w hw
      refine ⟨GaussianReflection w, ?_, ?_⟩
      · rcases hw with h | h
        · subst w
          exact Or.inl (by ext <;> simp [GaussianReflection] )
        · subst w
          exact Or.inr (by ext <;> simp [GaussianReflection] )
      · rfl
  | shift v =>
      intro w hw
      refine ⟨w, hw, ?_⟩
      simp [BandPackingSymmetryCircleAction]
  | comp a b iha ihb =>
      intro w hw
      obtain ⟨wb, hwb, hb⟩ := ihb w hw
      obtain ⟨wa, hwa, ha⟩ := iha wb hwb
      exact ⟨wa, hwa, by simpa [BandPackingSymmetryCircleAction, hb] using ha⟩

private theorem tileEmpty :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryTileAction a ⟨∅, x⟩
            = ⟨∅, BandPackingSymmetryVectorAction a x⟩ ) := by
  classical
  intro a
  induction a with
  | identity => intro x; rfl
  | negate => intro x; simp [BandPackingSymmetryTileAction, TileQuarterTurn,
      BandPackingSymmetryVectorAction]
  | conjugate =>
      intro x
      apply congrArg₂ ProtoTile.mk
      · simp [TileQuarterTurn, TileReflection]
      · ext <;> simp [TileQuarterTurn, TileReflection,
          GaussianQuarterTurn, GaussianReflection, BandPackingSymmetryVectorAction]
  | shift w => intro x; rfl
  | comp a b iha ihb =>
      intro x
      simp only [BandPackingSymmetryTileAction, ihb, iha,
        BandPackingSymmetryVectorAction]

private theorem zeroLine :
    (by
      classical
      exact
        ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), D.1 = 0 →
            TileOdometer D U k → ∃ w x, (w = 1 ∨ w = -1) ∧ D = (0, w) ∧ U = ⟨∅, x⟩ ∧ k.domain =
            {x} ) := by
  classical
  intro D U k hz ho
  cases ho with
  | line w x hw k hk => exact ⟨w, x, hw, rfl, rfl, hk⟩
  | unit z x U k hU hdom htrans => simp at hz
  | decompose hq hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope =>
      have hp := (ProperBandCurvatureStructure _ hq).1
      omega

private abbrev actionForward := BandPackingSymmetryDomainTransport.forward

private theorem actionDiff :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), (x ∈
            k.domain) → (BandPackingSymmetryVectorAction a x ∈
            (BandPackingSymmetryPartialOdometerAction a k).domain)) → (∀ (a :
            BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (l : PartialOdometer), ∀ (x :
            GaussianInt), (x ∈ k.domain) → ((x ∈ l.domain) →
            ((BandPackingSymmetryPartialOdometerAction a l).value
            (BandPackingSymmetryVectorAction a x) - (BandPackingSymmetryPartialOdometerAction a
            k).value (BandPackingSymmetryVectorAction a x) = l.value x - k.value x))) ) := by
  classical
  intro actionForward a k l x hk hl
  induction a generalizing k l x with
  | identity => rfl
  | shift w =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        hk, hl, ↓reduceIte]
      ring
  | negate =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem GaussianQuarterTurn hk,
        Finset.mem_image_of_mem GaussianQuarterTurn hl, ↓reduceIte]
      have hi : -GaussianQuarterTurn (GaussianQuarterTurn x) = x := by
        ext <;> simp [GaussianQuarterTurn]
      rw [hi]
  | conjugate =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) hk,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) hl, ↓reduceIte]
      have hi : -GaussianReflection (-GaussianReflection x) = x := by
        ext <;> simp [GaussianReflection]
      rw [hi]
  | comp a b iha ihb =>
      have hbK := actionForward b k x hk
      have hbL := actionForward b l x hl
      simpa [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction]
        using iha (BandPackingSymmetryPartialOdometerAction b k)
          (BandPackingSymmetryPartialOdometerAction b l)
          (BandPackingSymmetryVectorAction b x) hbK hbL |>.trans
            (ihb k l x hk hl)

private theorem lineCov :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (w : GaussianInt), (w = 1 ∨ w = -1) → ∃ w', (w' = 1 ∨ w'
            = -1) ∧ BandPackingSymmetryCircleAction a (0, w) = (0, w')) → ((∀ (a :
            BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryTileAction a ⟨∅, x⟩ =
            ⟨∅, BandPackingSymmetryVectorAction a x⟩) → ((∀ (D : CircleCoordinates), ∀ (U :
            ProtoTile), ∀ (k : PartialOdometer), D.1 = 0 → TileOdometer D U k → ∃ w x, (w = 1 ∨ w
            = -1) ∧ D = (0, w) ∧ U = ⟨∅, x⟩ ∧ k.domain = {x}) → (∀ (w : GaussianInt), ∀ (x :
            GaussianInt), (w = 1 ∨ w = -1) → (∀ (k : PartialOdometer), k.domain = {x} → ∀ a :
            BandPackingSymmetry, TileOdometer (BandPackingSymmetryCircleAction a (0, w))
            (BandPackingSymmetryTileAction a ⟨∅, x⟩) (BandPackingSymmetryPartialOdometerAction a
            k))))) ) := by
  classical
  intro lineCircle tileEmpty zeroLine w x hw k hk a
  induction a generalizing w x k with
  | identity =>
      simpa [BandPackingSymmetryCircleAction, BandPackingSymmetryTileAction,
        BandPackingSymmetryPartialOdometerAction] using
        TileOdometer.line w x hw k hk
  | negate =>
      have hw' : -w = 1 ∨ -w = -1 := by
        rcases hw with h | h <;> subst w <;> first | exact Or.inr rfl | exact Or.inl rfl
      have ht : BandPackingSymmetryTileAction .negate ⟨∅, x⟩ =
          ⟨∅, GaussianQuarterTurn x⟩ := by simp [BandPackingSymmetryTileAction, TileQuarterTurn]
      rw [ht]
      simpa [BandPackingSymmetryCircleAction, BandPackingSymmetryPartialOdometerAction,
        hk] using TileOdometer.line (-w) (GaussianQuarterTurn x) hw'
          (BandPackingSymmetryPartialOdometerAction .negate k) (by
            simp [BandPackingSymmetryPartialOdometerAction, hk])
  | conjugate =>
      have hw' : GaussianReflection w = 1 ∨ GaussianReflection w = -1 := by
        rcases hw with h | h
        · subst w
          exact Or.inl (by ext <;> simp [GaussianReflection] )
        · subst w
          exact Or.inr (by ext <;> simp [GaussianReflection] )
      have ht : BandPackingSymmetryTileAction .conjugate ⟨∅, x⟩ =
          ⟨∅, -GaussianReflection x⟩ := by
        rw [tileEmpty]
        simp [BandPackingSymmetryVectorAction]
      rw [ht]
      simpa [BandPackingSymmetryCircleAction, BandPackingSymmetryPartialOdometerAction,
        GaussianReflection, hk] using
        TileOdometer.line (GaussianReflection w) (-GaussianReflection x) hw'
          (BandPackingSymmetryPartialOdometerAction .conjugate k) (by
            simp [BandPackingSymmetryPartialOdometerAction, hk])
  | shift v =>
      simpa [BandPackingSymmetryCircleAction, BandPackingSymmetryTileAction,
        BandPackingSymmetryPartialOdometerAction, hk] using
        TileOdometer.line w x hw
          (BandPackingSymmetryPartialOdometerAction (.shift v) k) (by
            simp [BandPackingSymmetryPartialOdometerAction, hk])
  | comp a b iha ihb =>
      have mid := ihb w x hw k hk
      obtain ⟨wm, hwm, hcircle⟩ := lineCircle b w hw
      obtain ⟨w', x', hw', hC, hT, hk'⟩ :=
        zeroLine _ _ _ (by simp [hcircle]) mid
      have htile : BandPackingSymmetryTileAction b ⟨∅, x⟩ = ⟨∅, x'⟩ := hT
      change TileOdometer
        (BandPackingSymmetryCircleAction a (BandPackingSymmetryCircleAction b (0, w)))
        (BandPackingSymmetryTileAction a (BandPackingSymmetryTileAction b ⟨∅, x⟩))
        (BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b k))
      rw [hC, htile]
      exact iha w' x' hw' _ hk'

private abbrev circleCurvature := ApollonianSuperharmonic.BandPackingSymmetryCurvature.preserved

private theorem extractUnit :
    (by
      classical
      exact
        ∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), D.1 = 1 →
            TileOdometer D U k → ∃ z x, D = (1, 1 + 2 * z) ∧ U.cells = {x} ∧ (k.domain : Set
            GaussianInt) = FootprintVertices U ∧ OdometerTranslation k (CurvatureOneOdometer z) )
            := by
  classical
  intro D U k hcurv ho
  cases ho with
  | line w x hw l hdom => simp at hcurv
  | unit z x V l hV hdom htrans => exact ⟨z, x, rfl, hV, hdom, htrans⟩
  | @decompose q hq S V hs l hV hsub hcells hfoot hcent hdom hvalue hcompat hslope =>
      have hparent : 1 < (q 0).1 := by
        have hpAll : ∃ i : Fin 3, 0 < (q i.succ).1 := by
          have hp := (ProperBandCurvatureStructure q hq).2.1
          by_cases h0 : 0 < (q (0 : Fin 3).succ).1
          · exact ⟨0, h0⟩
          by_cases h1 : 0 < (q (1 : Fin 3).succ).1
          · exact ⟨1, h1⟩
          have n0 := hp 0
          have n1 := hp 1
          have z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
          have z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
          exact ((by decide : (0 : Fin 3) ≠ 1)
            ((ProperBandCurvatureStructure q hq).2.2 0 1 z0 z1)).elim
        obtain ⟨i, hi⟩ := hpAll
        have hb := hq.2 i
        omega
      omega

private theorem affineMix :
    (by
      classical
      exact
        let symmetryMix : Bool → GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun r z => if r then
            (z.1 + GaussianQuarterTurn z.1, z.2 - GaussianQuarterTurn z.2)
          else (z.1 - GaussianQuarterTurn z.1, z.2 + GaussianQuarterTurn z.2)
        ∀ (a : BandPackingSymmetry), ∀ (r : Bool), ∀ (z : GaussianInt × GaussianInt),
            BandPackingSymmetryAffineVectorAction a (symmetryMix r z) = symmetryMix (xor r
            (BandPackingSymmetryReversesOrientation a)) (BandPackingSymmetryAffineVectorAction a
            z) ) := by
  classical
  intro symmetryMix a
  induction a with
  | identity => intro r z; cases r <;> rfl
  | shift t =>
      intro r z
      rcases t with ⟨tr, ti⟩
      rcases z with ⟨v, w⟩
      cases r <;> rcases v with ⟨vr, vi⟩ <;> rcases w with ⟨wr, wi⟩ <;>
        ext <;> simp [symmetryMix, BandPackingSymmetryAffineVectorAction,
          BandPackingSymmetryReversesOrientation, GaussianQuarterTurn,
          GaussianReflection] <;> ring
  | negate =>
      intro r z
      rcases z with ⟨v, w⟩
      cases r <;> rcases v with ⟨vr, vi⟩ <;> rcases w with ⟨wr, wi⟩ <;>
        ext <;> simp [symmetryMix, BandPackingSymmetryAffineVectorAction,
          BandPackingSymmetryReversesOrientation, GaussianQuarterTurn] <;> ring
  | conjugate =>
      intro r z
      rcases z with ⟨v, w⟩
      cases r <;> rcases v with ⟨vr, vi⟩ <;> rcases w with ⟨wr, wi⟩ <;>
        ext <;> simp [symmetryMix, BandPackingSymmetryAffineVectorAction,
          BandPackingSymmetryReversesOrientation, GaussianQuarterTurn,
          GaussianReflection] <;> ring
  | comp a b iha ihb =>
      intro r z
      change BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b (symmetryMix r z)) =
        symmetryMix (xor r (xor (BandPackingSymmetryReversesOrientation a)
          (BandPackingSymmetryReversesOrientation b)))
          (BandPackingSymmetryAffineVectorAction a
            (BandPackingSymmetryAffineVectorAction b z))
      rw [ihb r z, iha]
      simp [Bool.xor_comm, Bool.xor_left_comm,
        ]

private theorem triangular :
    (by
      classical
      exact
        ∀ (n : ℤ), (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n ) := by
  classical
  intro n
  rw [show (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 by ring]
  exact Int.add_mul_ediv_right _ _ (by norm_num)

private theorem shiftDx :
    (by
      classical
      exact
        ∀ (wr : ℤ), ∀ (wi : ℤ), (∀ (n : ℤ), (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n) → (∀
            (y : GaussianInt), BandPackingShiftPotential ⟨wr, wi⟩ (y + 1) -
            BandPackingShiftPotential ⟨wr, wi⟩ y = wr * y.re + wi * y.im) ) := by
  classical
  intro wr wi triangular y
  simp only [BandPackingShiftPotential, Zsqrtd.re_add,
    Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one, add_zero]
  rw [triangular]
  ring

private theorem shiftDy :
    (by
      classical
      exact
        ∀ (wr : ℤ), ∀ (wi : ℤ), (∀ (n : ℤ), (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n) → (∀
            (y : GaussianInt), BandPackingShiftPotential ⟨wr, wi⟩ (y + ⟨0, 1⟩) -
            BandPackingShiftPotential ⟨wr, wi⟩ y = -wr * y.im + wi * y.re) ) := by
  classical
  intro wr wi triangular y
  simp only [BandPackingShiftPotential, Zsqrtd.re_add,
    Zsqrtd.im_add, add_zero]
  rw [triangular]
  ring

private theorem hcorner :
    (by
      classical
      exact
        ∀ (wr : ℤ), ∀ (wi : ℤ), (∀ (y : GaussianInt), BandPackingShiftPotential ⟨wr, wi⟩ (y + 1)
            - BandPackingShiftPotential ⟨wr, wi⟩ y = wr * y.re + wi * y.im) → ((∀ (y :
            GaussianInt), BandPackingShiftPotential ⟨wr, wi⟩ (y + ⟨0, 1⟩) -
            BandPackingShiftPotential ⟨wr, wi⟩ y = -wr * y.im + wi * y.re) → (∀ (v : GaussianInt),
        let d1 := BandPackingShiftPotential ⟨wr, wi⟩ (v + 1) -
          BandPackingShiftPotential ⟨wr, wi⟩ v
        let d2 := BandPackingShiftPotential ⟨wr, wi⟩ (v + ⟨0, 1⟩) -
          BandPackingShiftPotential ⟨wr, wi⟩ v
        BandPackingShiftPotential ⟨wr, wi⟩ (v + 1 + ⟨0, 1⟩) = BandPackingShiftPotential ⟨wr, wi⟩
            v + d1 + d2 + wi)) ) := by
  classical
  intro wr wi shiftDx shiftDy v d1 d2
  have hdx := shiftDx (v + ⟨0, 1⟩)
  have hdx0 := shiftDx v
  have hdy0 := shiftDy v
  rw [show v + ⟨0, 1⟩ + 1 = v + 1 + ⟨0, 1⟩ by abel] at hdx
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    add_zero] at hdx
  have hd1 : d1 = wr * v.re + wi * v.im := by
    simpa [d1] using hdx0
  have hv : BandPackingShiftPotential ⟨wr, wi⟩ (v + ⟨0, 1⟩) =
      BandPackingShiftPotential ⟨wr, wi⟩ v + d2 := by
    dsimp [d2]
    linarith [hdy0]
  have hd1corner : wr * v.re + wi * (v.im + 1) = d1 + wi := by
    rw [hd1]
    ring
  calc
    BandPackingShiftPotential ⟨wr, wi⟩ (v + 1 + ⟨0, 1⟩) =
        BandPackingShiftPotential ⟨wr, wi⟩ (v + ⟨0, 1⟩) +
          (wr * v.re + wi * (v.im + 1)) := by linarith
    _ = BandPackingShiftPotential ⟨wr, wi⟩ v + d2 + d1 + wi := by
      rw [hv, hd1corner]
      ring
    _ = BandPackingShiftPotential ⟨wr, wi⟩ v + d1 + d2 + wi := by ring

private theorem hpsi :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (wr : ℤ), ∀ (wi : ℤ), ∀ (v : GaussianInt),
        let d1 := BandPackingShiftPotential ⟨wr, wi⟩ (v + 1) -
          BandPackingShiftPotential ⟨wr, wi⟩ v
        let d2 := BandPackingShiftPotential ⟨wr, wi⟩ (v + ⟨0, 1⟩) -
          BandPackingShiftPotential ⟨wr, wi⟩ v
        let d : GaussianInt := ⟨d1, d2⟩
        (BandPackingShiftPotential ⟨wr, wi⟩ (v + 1 + ⟨0, 1⟩) = BandPackingShiftPotential ⟨wr, wi⟩
            v + d1 + d2 + wi) → (∀ (r : GaussianInt), (r ∈ (CurvatureOneOdometer z).domain) →
            (BandPackingShiftPotential ⟨wr, wi⟩ (v + r) = wi * r.re * r.im + d.re * (v + r).re +
            d.im * (v + r).im + BandPackingShiftPotential ⟨wr, wi⟩ v - d.re * v.re - d.im *
            v.im)) ) := by
  classical
  intro z wr wi v d1 d2 d hcorner r hr
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with hr | hr | hr | hr
  · subst r
    simp [d, d1, d2]
    ring
  · subst r
    simp [d, d1, d2]
    ring
  · subst r
    simp [d, d1, d2]
    ring
  · subst r
    rw [show v + (1 + ⟨0, 1⟩) = v + 1 + ⟨0, 1⟩ by abel,
      hcorner]
    simp [d, d1, d2]
    ring

private theorem hcurvAt595 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (wr : ℤ), ∀ (wi : ℤ), ∀ (r : GaussianInt), (r ∈
            (CurvatureOneOdometer z).domain) → ((CurvatureOneOdometer (z + ⟨wr, wi⟩)).value r =
            (CurvatureOneOdometer z).value r + wi * r.re * r.im) ) := by
  classical
  intro z wr wi r hr
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with hr | hr | hr | hr
  · subst r
    simp [CurvatureOneOdometer, Zsqrtd.ext_iff]
  · subst r
    simp [CurvatureOneOdometer, Zsqrtd.ext_iff]
  · subst r
    simp [CurvatureOneOdometer, Zsqrtd.ext_iff]
  · subst r
    simp [CurvatureOneOdometer, Zsqrtd.im_add]


private theorem hCAt611 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (wr : ℤ), ∀ (wi : ℤ), BandPackingSymmetryCircleAction (.shift ⟨wr,
            wi⟩) (1, 1 + 2 * z) = (1, 1 + 2 * (z + ⟨wr, wi⟩)) ) := by
  classical
  intro z wr wi
  apply Prod.ext
  · rfl
  · simp [BandPackingSymmetryCircleAction]
    ring

private theorem hyk :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (wr : ℤ), ∀ (wi : ℤ), ∀ (y : GaussianInt), (y ∈
            (BandPackingSymmetryPartialOdometerAction (BandPackingSymmetry.shift (⟨wr, wi⟩ :
            GaussianInt)) k).domain) → (y ∈ k.domain) ) := by
  classical
  intro k wr wi y hy
  change y ∈ k.domain at hy
  exact hy

private theorem hcellAt653 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells = {x}) → ((TileQuarterTurn U).cells =
            {GaussianQuarterTurn x - 1}) ) := by
  classical
  intro U x hU
  rw [(TileQuarterTurnFormulas U).1, hU]
  simp

private theorem hdomainAt657 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FootprintVertices U) → (((BandPackingSymmetryPartialOdometerAction .negate k).domain
            : Set GaussianInt) = FootprintVertices (TileQuarterTurn U)) ) := by
  classical
  intro U k hdom
  rw [(BandPackingSymmetryPartialOdometerActionFormulas
    .negate k k).1, (TileQuarterTurnFormulas U).2.2.2.2.2.1,
    hdom]
  simp [BandPackingSymmetryVectorAction]

private theorem hdomainUnitAt664 :
    (by
      classical
      exact
        ∀ (z : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (r : GaussianInt), I - GaussianQuarterTurn r ∈ (CurvatureOneOdometer z).domain ↔ r ∈
            (CurvatureOneOdometer (-z - 1)).domain ) := by
  classical
  intro z I r
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr
    all_goals
      rcases r with ⟨rr, ri⟩
      simp [GaussianQuarterTurn, I, Zsqrtd.ext_iff] at hr ⊢
      omega
  · intro hr
    rcases hr with hr | hr | hr | hr
    all_goals
      rcases r with ⟨rr, ri⟩
      simp [GaussianQuarterTurn, I, Zsqrtd.ext_iff] at hr ⊢
      omega

private theorem hunitValueAt682 :
    (by
      classical
      exact
        ∀ (z : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (r : GaussianInt), (r ∈ (CurvatureOneOdometer z).domain) → ((CurvatureOneOdometer
            z).value (I - GaussianQuarterTurn r) = (CurvatureOneOdometer (-z - 1)).value r + z.im
            * r.im) ) := by
  classical
  intro z I r hr
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with hr | hr | hr | hr
  all_goals
    rcases r with ⟨rr, ri⟩
    simp [CurvatureOneOdometer, GaussianQuarterTurn, I,
      Zsqrtd.ext_iff] at hr ⊢
    simp [hr]

private theorem hinverseAt694 :
    (by
      classical
      exact
        ∀ (v : GaussianInt),
        let I : GaussianInt := ⟨0, 1⟩
        let vn := GaussianQuarterTurn v - 1
        ∀ (y : GaussianInt), -GaussianQuarterTurn y - v = I - GaussianQuarterTurn (y - vn) ) := by
  classical
  intro v I vn y
  dsimp [vn, I]
  ext <;> simp [GaussianQuarterTurn]; ring

private theorem himageAt698 :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (y : GaussianInt), y ∈ k.domain.image GaussianQuarterTurn ↔
            -GaussianQuarterTurn y ∈ k.domain ) := by
  classical
  intro k y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x0, hx0, hxy⟩
    have he : -GaussianQuarterTurn y = x0 := by
      rw [← hxy]
      ext <;> simp [GaussianQuarterTurn]
    simpa [he] using hx0
  · intro hy
    refine ⟨-GaussianQuarterTurn y, hy, ?_⟩
    ext <;> simp [GaussianQuarterTurn]

private theorem htrans'At711 :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ∀ (a0 : GaussianInt),
            ∀ (b0 : ℤ), (∀ (x : GaussianInt), x ∈ k.domain ↔ x - v ∈ (CurvatureOneOdometer
            z).domain) → ((∀ x ∈ k.domain, k.value x = (CurvatureOneOdometer z).value (x - v) +
            a0.re * x.re + a0.im * x.im + b0) → (
        let I : GaussianInt := ⟨0, 1⟩
        let vn := GaussianQuarterTurn v - 1
        (∀ (r : GaussianInt), I - GaussianQuarterTurn r ∈ (CurvatureOneOdometer z).domain ↔ r ∈
            (CurvatureOneOdometer (-z - 1)).domain) → ((∀ (r : GaussianInt), (r ∈
            (CurvatureOneOdometer z).domain) → ((CurvatureOneOdometer z).value (I -
            GaussianQuarterTurn r) = (CurvatureOneOdometer (-z - 1)).value r + z.im * r.im)) →
            ((∀ (y : GaussianInt), -GaussianQuarterTurn y - v = I - GaussianQuarterTurn (y - vn))
            → ((∀ (y : GaussianInt), y ∈ k.domain.image GaussianQuarterTurn ↔
            -GaussianQuarterTurn y ∈ k.domain) → (OdometerTranslation
            (BandPackingSymmetryPartialOdometerAction .negate k) (CurvatureOneOdometer (-z -
            1)))))))) ) := by
  classical
  intro k z v a0 b0 hvdom hvval I vn hdomainUnit hunitValue hinverse himage
  let an := GaussianQuarterTurn a0 + ⟨0, z.im⟩
  let bn := b0 - z.im * vn.im
  refine ⟨vn, an, bn, ?_, ?_⟩
  · intro y
    change y ∈ k.domain.image GaussianQuarterTurn ↔
      y - vn ∈ (CurvatureOneOdometer (-z - 1)).domain
    rw [himage, hvdom, hinverse]
    exact hdomainUnit (y - vn)
  · intro y hy
    have hyold : -GaussianQuarterTurn y ∈ k.domain :=
      (himage y).mp hy
    have hrTarget : y - vn ∈
        (CurvatureOneOdometer (-z - 1)).domain := by
      have h := (hvdom (-GaussianQuarterTurn y)).mp hyold
      rw [hinverse] at h
      exact (hdomainUnit (y - vn)).mp h
    have hr : y - vn ∈ (CurvatureOneOdometer z).domain := by
      simpa [CurvatureOneOdometer] using hrTarget
    have hval := hvval (-GaussianQuarterTurn y) hyold
    have hcanon := hunitValue (y - vn) hr
    have hact := (BandPackingSymmetryPartialOdometerActionFormulas
      .negate k k).2.2.2.1 y hy
    rw [hact, hval, hinverse, hcanon]
    dsimp [an, bn, vn]
    simp [GaussianQuarterTurn]
    ring

private theorem hCAt738 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), BandPackingSymmetryCircleAction .negate (1, 1 + 2 * z) = (1, 1 + 2 *
            (-z - 1)) ) := by
  classical
  intro z
  ext <;> simp [BandPackingSymmetryCircleAction]; ring

private theorem hcellAt753 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells = {x}) → ((BandPackingSymmetryTileAction
            .conjugate U).cells = {-GaussianReflection x - 1}) ) := by
  classical
  intro U x hU
  simp only [BandPackingSymmetryTileAction]
  rw [(TileQuarterTurnFormulas
    (TileQuarterTurn (TileReflection U))).1,
    (TileQuarterTurnFormulas (TileReflection U)).1,
    (TileReflectionFormulas U).1, hU]
  simp [GaussianQuarterTurn, GaussianReflection,
    Finset.image_singleton, Zsqrtd.ext_iff]

private theorem hdomainAt763 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FootprintVertices U) → (((BandPackingSymmetryPartialOdometerAction .conjugate
            k).domain : Set GaussianInt) = FootprintVertices (BandPackingSymmetryTileAction
            .conjugate U)) ) := by
  classical
  intro U k hdom
  rw [(BandPackingSymmetryPartialOdometerActionFormulas
    .conjugate k k).1]
  change (fun y => -GaussianReflection y) '' (k.domain : Set GaussianInt) =
    FootprintVertices (TileQuarterTurn
      (TileQuarterTurn (TileReflection U)))
  rw [(TileQuarterTurnFormulas
      (TileQuarterTurn (TileReflection U))).2.2.2.2.2.1,
    (TileQuarterTurnFormulas (TileReflection U)).2.2.2.2.2.1,
    (TileReflectionFormulas U).2.2.2.2.2.1, hdom]
  rw [Set.image_image, Set.image_image]
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by
      ext <;> simp [GaussianQuarterTurn, GaussianReflection] ⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    rw [← hxy]
    ext <;> simp [GaussianQuarterTurn, GaussianReflection]

private theorem hdomainUnitAt787 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (r : GaussianInt), 1 - GaussianReflection r ∈
            (CurvatureOneOdometer z).domain ↔ r ∈ (CurvatureOneOdometer (GaussianReflection
            z)).domain ) := by
  classical
  intro z r
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr
    all_goals
      rcases r with ⟨rr, ri⟩
      simp [GaussianReflection, Zsqrtd.ext_iff] at hr ⊢
      omega
  · intro hr
    rcases hr with hr | hr | hr | hr
    all_goals
      rcases r with ⟨rr, ri⟩
      simp [GaussianReflection, Zsqrtd.ext_iff] at hr ⊢
      omega

private theorem hunitValueAt805 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (r : GaussianInt), (r ∈ (CurvatureOneOdometer z).domain) →
            ((CurvatureOneOdometer z).value (1 - GaussianReflection r) = (CurvatureOneOdometer
            (GaussianReflection z)).value r + z.im * r.im) ) := by
  classical
  intro z r hr
  simp only [CurvatureOneOdometer, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with hr | hr | hr | hr
  all_goals
    rcases r with ⟨rr, ri⟩
    simp [CurvatureOneOdometer, GaussianReflection,
      Zsqrtd.ext_iff] at hr ⊢
    simp [hr]

private theorem hinverseAt818 :
    (by
      classical
      exact
        ∀ (v : GaussianInt),
        let vk := -GaussianReflection v - 1
        ∀ (y : GaussianInt), -GaussianReflection y - v = 1 - GaussianReflection (y - vk) ) := by
  classical
  intro v vk y
  dsimp [vk]
  ext <;> simp [GaussianReflection]; ring

private theorem himageAt823 :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (y : GaussianInt), y ∈ k.domain.image (fun x =>
            -GaussianReflection x) ↔ -GaussianReflection y ∈ k.domain ) := by
  classical
  intro k y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x0, hx0, hxy⟩
    have he : -GaussianReflection y = x0 := by
      rw [← hxy]
      ext <;> simp [GaussianReflection]
    simpa [he] using hx0
  · intro hy
    refine ⟨-GaussianReflection y, hy, ?_⟩
    ext <;> simp [GaussianReflection]

private theorem htrans'At836 :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (z : GaussianInt), ∀ (v : GaussianInt), ∀ (a0 : GaussianInt),
            ∀ (b0 : ℤ), (∀ (x : GaussianInt), x ∈ k.domain ↔ x - v ∈ (CurvatureOneOdometer
            z).domain) → ((∀ x ∈ k.domain, k.value x = (CurvatureOneOdometer z).value (x - v) +
            a0.re * x.re + a0.im * x.im + b0) → (
        let vk := -GaussianReflection v - 1
        (∀ (r : GaussianInt), 1 - GaussianReflection r ∈ (CurvatureOneOdometer z).domain ↔ r ∈
            (CurvatureOneOdometer (GaussianReflection z)).domain) → ((∀ (r : GaussianInt), (r ∈
            (CurvatureOneOdometer z).domain) → ((CurvatureOneOdometer z).value (1 -
            GaussianReflection r) = (CurvatureOneOdometer (GaussianReflection z)).value r + z.im
            * r.im)) → ((∀ (y : GaussianInt), -GaussianReflection y - v = 1 - GaussianReflection
            (y - vk)) → ((∀ (y : GaussianInt), y ∈ k.domain.image (fun x => -GaussianReflection
            x) ↔ -GaussianReflection y ∈ k.domain) → (OdometerTranslation
            (BandPackingSymmetryPartialOdometerAction .conjugate k) (CurvatureOneOdometer
            (GaussianReflection z)))))))) ) := by
  classical
  intro k z v a0 b0 hvdom hvval vk hdomainUnit hunitValue hinverse himage
  let ak := -GaussianReflection a0 + ⟨0, z.im⟩
  let bk := b0 - z.im * vk.im
  refine ⟨vk, ak, bk, ?_, ?_⟩
  · intro y
    change y ∈ k.domain.image (fun x => -GaussianReflection x) ↔
      y - vk ∈
        (CurvatureOneOdometer (GaussianReflection z)).domain
    rw [himage, hvdom, hinverse]
    exact hdomainUnit (y - vk)
  · intro y hy
    have hyold : -GaussianReflection y ∈ k.domain :=
      (himage y).mp hy
    have hrTarget : y - vk ∈
        (CurvatureOneOdometer (GaussianReflection z)).domain := by
      have h := (hvdom (-GaussianReflection y)).mp hyold
      rw [hinverse] at h
      exact (hdomainUnit (y - vk)).mp h
    have hr : y - vk ∈ (CurvatureOneOdometer z).domain := by
      simpa [CurvatureOneOdometer] using hrTarget
    have hval := hvval (-GaussianReflection y) hyold
    have hcanon := hunitValue (y - vk) hr
    have hact := (BandPackingSymmetryPartialOdometerActionFormulas
      .conjugate k k).2.2.2.2.1 y hy
    rw [hact, hval, hinverse, hcanon]
    dsimp [ak, bk, vk]
    simp [GaussianReflection]
    ring

private theorem hCAt864 :
    (by
      classical
      exact
        ∀ (z : GaussianInt), BandPackingSymmetryCircleAction .conjugate (1, 1 + 2 * z) = (1, 1 +
            2 * GaussianReflection z) ) := by
  classical
  intro z
  ext <;> simp [BandPackingSymmetryCircleAction,
    GaussianReflection]

private theorem hocc :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s
            : Bool), TileOdometer (q i.succ) (S i s) (hs i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), FootprintVertices (S i s) ⊆ FootprintVertices U) → ((∀ (i : Fin (3 : ℕ)), ∀ (s
            : Bool), TileCentroid (S i s) - TileCentroid U = (if s = true then (1 : ℝ) else (-1 :
            ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).1))) → (∀ i, ∀ s, BandSubtileOccurrence q U i s (S i s)))) ) := by
  classical
  intro U q S hs hsub hfoot hcentroid i s
  exact ⟨TileOdometerBandPrototile (q i.succ) (S i s) (hs i s)
    (hsub i s), hfoot i s, hcentroid i s⟩

private theorem hparentAt910 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let A := BandPackingSymmetryCircleAction
        let q' := Q a q
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        (-(1 : Fin 3) = 2) → ((-(2 : Fin 3) = 1) → (∀ (i : Fin 3), q' (sigma i).succ = A a (q
            i.succ))) ) := by
  classical
  intro q a Q A q' sigma hneg1 hneg2 i
  dsimp [q', sigma, Q, A]
  cases hrev : BandPackingSymmetryReversesOrientation a <;>
    fin_cases i <;>
    simp [BandPackingSymmetryQuadrupleAction, hrev, hneg1, hneg2]

private theorem hT' :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (BandPrototile (q (0 : Fin (4
            : ℕ))) U) → (∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let B := BandPackingSymmetryTileAction
        let q' := Q a q
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction a C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction a C) (BandPackingSymmetryTileAction a T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation a = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase a q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction a (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction a q)
            (BandPackingSymmetryTileAction a T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction a T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S' i
            s).cells) → (BandPrototile (q' 0) (B a U))) ) := by
  classical
  intro U q hT a Q B q' cov
  have ht := cov.2.1 (q 0) U
  have ht' := ht.mp hT
  simpa [q', Q, B, BandPackingSymmetryQuadrupleAction] using ht'

private theorem hsub' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
            ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer),
              (∀ (i : Fin (3 : ℕ)),
                  ∀ (s : Bool),
                    ∀ (a : BandPackingSymmetry),
                      TileOdometer (BandPackingSymmetryCircleAction a (q i.succ))
                        (BandPackingSymmetryTileAction a (S i s))
                        (BandPackingSymmetryPartialOdometerAction a (hs i s))) →
                ∀ (a : BandPackingSymmetry),
                  let Q := BandPackingSymmetryQuadrupleAction
                  let A := BandPackingSymmetryCircleAction
                  let P := BandPackingSymmetryPartialOdometerAction
                  let q' := Q a q
                  let sigma : Fin 3 → Fin 3 := fun i =>
                    if BandPackingSymmetryReversesOrientation a then -i else i
                  ∀ (delta : Bool),
                    ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
                      ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
                        (∀ (i : Fin (3 : ℕ)),
                            ∀ (s : Bool),
                              (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s) =
                                ((fun (i : Fin (3 : ℕ)) =>
                                if BandPackingSymmetryReversesOrientation a = true then -i
                              else i)
                                i,
                                s ^^ delta)) →
                          (∀ (i : Fin (3 : ℕ)),
                              ∀ (s : Bool),
                                S'
                                ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1
                                ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).2 =
                                BandPackingSymmetryTileAction a (S i s)) →
                            (∀ (i : Fin 3), q' (sigma i).succ = A a (q i.succ)) →
                              let hs' : Fin 3 → Bool → PartialOdometer := fun j s =>
                                P a (hs (e.symm (j, s)).1 (e.symm (j, s)).2)
                              ∀ j, ∀ s, TileOdometer (q' j.succ) (S' j s) (hs' j s)
    ) := by
  classical
  intro q S hs ih a Q A P q' sigma delta e S' he hS hparent hs' j s
  let B := BandPackingSymmetryTileAction
  let p := e.symm (j, s)
  have hep : e p = (j, s) := e.apply_symm_apply (j, s)
  have hchildT : S' j s = B a (S p.1 p.2) := by
    have hh := hS p.1 p.2
    simpa [p, hep] using hh
  have hchildC : q' j.succ = A a (q p.1.succ) := by
    have := hparent p.1
    have hpair : (sigma p.1, xor p.2 delta) = (j, s) := by
      calc
        (sigma p.1, xor p.2 delta) = e p := by
          simpa [p] using (he p.1 p.2).symm
        _ = (j, s) := hep
    have hidx : sigma p.1 = j := congrArg Prod.fst hpair
    simpa [p, hidx] using this
  rw [hchildT, hchildC]
  exact ih p.1 p.2 a

private theorem hdom' :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (x :
            GaussianInt), x ∈ h.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (hs i s).domain) →
            (∀ (a : BandPackingSymmetry),
        let P := BandPackingSymmetryPartialOdometerAction
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
        let hs' : Fin 3 → Bool → PartialOdometer := fun j s =>
          P a (hs (e.symm (j, s)).1 (e.symm (j, s)).2)
        ∀ y, y ∈ (P a h).domain ↔ ∃ j s, y ∈ (hs' j s).domain) ) := by
  classical
  intro h hs hdom a P e hs' y
  change y ∈ ((P a h).domain : Set GaussianInt) ↔ _
  rw [(BandPackingSymmetryPartialOdometerActionFormulas a h h).1]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (hdom x).mp hx with ⟨i, s, hxs⟩
    refine ⟨(e (i, s)).1, (e (i, s)).2, ?_⟩
    change BandPackingSymmetryVectorAction a x ∈
      ((P a (hs (e.symm ((e (i, s)).1, (e (i, s)).2)).1
        (e.symm ((e (i, s)).1, (e (i, s)).2)).2)).domain : Set GaussianInt)
    rw [e.symm_apply_apply]
    rw [(BandPackingSymmetryPartialOdometerActionFormulas a
      (hs i s) (hs i s)).1]
    exact ⟨x, hxs, rfl⟩
  · rintro ⟨j, s, hy⟩
    let p := e.symm (j, s)
    change y ∈ ((P a (hs p.1 p.2)).domain : Set GaussianInt) at hy
    rw [(BandPackingSymmetryPartialOdometerActionFormulas a
      (hs p.1 p.2) (hs p.1 p.2)).1] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, (hdom x).mpr ⟨p.1, p.2, hx⟩, rfl⟩

private theorem hvalue' :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), (∀ (a : BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (l :
            PartialOdometer), ∀ (x : GaussianInt), (x ∈ k.domain) → ((x ∈ l.domain) →
            ((BandPackingSymmetryPartialOdometerAction a l).value
            (BandPackingSymmetryVectorAction a x) - (BandPackingSymmetryPartialOdometerAction a
            k).value (BandPackingSymmetryVectorAction a x) = l.value x - k.value x))) → (∀ (hs :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (x : GaussianInt), x ∈ h.domain ↔ ∃ (i :
            Fin (3 : ℕ)) (s : Bool), x ∈ (hs i s).domain) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            ∀ x ∈ (hs i s).domain, h.value x = (hs i s).value x) → (∀ (a : BandPackingSymmetry),
        let P := BandPackingSymmetryPartialOdometerAction
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
        let hs' : Fin 3 → Bool → PartialOdometer := fun j s =>
          P a (hs (e.symm (j, s)).1 (e.symm (j, s)).2)
        ∀ j, ∀ s, ∀ y, y ∈ (hs' j s).domain → (P a h).value y = (hs' j s).value y))) ) := by
  classical
  intro h actionDiff hs hdom hvalue a P e hs' j s y hy
  let p := e.symm (j, s)
  change y ∈ ((P a (hs p.1 p.2)).domain : Set GaussianInt) at hy
  rw [(BandPackingSymmetryPartialOdometerActionFormulas a
    (hs p.1 p.2) (hs p.1 p.2)).1] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxOuter : x ∈ h.domain := (hdom x).mpr ⟨p.1, p.2, hx⟩
  have hd := actionDiff a h (hs p.1 p.2) x hxOuter hx
  rw [hvalue p.1 p.2 x hx] at hd
  simp only [sub_self] at hd
  exact (sub_eq_zero.mp hd).symm

private theorem hcompat' :
    (by
      classical
      exact
        ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j :
            Fin (3 : ℕ)), ∀ (t : Bool), OdometerCompatibility (hs i s) (hs j t)) → (∀ (a :
            BandPackingSymmetry),
        let P := BandPackingSymmetryPartialOdometerAction
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
        let hs' : Fin 3 → Bool → PartialOdometer := fun j s =>
          P a (hs (e.symm (j, s)).1 (e.symm (j, s)).2)
        ∀ i, ∀ s, ∀ j, ∀ t, OdometerCompatibility (hs' i s) (hs' j t)) ) := by
  classical
  intro hs hcompat a P e hs' i s j t
  let p := e.symm (i, s)
  let r := e.symm (j, t)
  apply (BandPackingSymmetryPartialOdometerActionFormulas a
    (hs p.1 p.2) (hs r.1 r.2)).2.2.2.2.2.2.1.mpr
  exact hcompat p.1 p.2 r.1 r.2

private theorem hpairAt1015 :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry),
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        ∀ (delta : Bool), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin (3 : ℕ)),
            ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s) = ((fun (i : Fin
            (3 : ℕ)) => if BandPackingSymmetryReversesOrientation a = true then -i else i) i, s
            ^^ delta)) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        (e p = (i, s)) → ((sigma p.1, xor p.2 delta) = (i, s))) ) := by
  classical
  intro a sigma delta e he i s p hep
  calc
    (sigma p.1, xor p.2 delta) = e p := by
      simpa [p] using (he p.1 p.2).symm
    _ = (i, s) := hep

private theorem hcurvAt1021 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let A := BandPackingSymmetryCircleAction
        let q' := Q a q
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction a C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction a C) (BandPackingSymmetryTileAction a T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation a = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase a q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction a (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction a q)
            (BandPackingSymmetryTileAction a T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction a T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S' i
            s).cells) → (∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), (∀ (i : Fin 3), q'
            (sigma i).succ = A a (q i.succ)) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        (sigma p.1 = i) → ((q' i.succ).1 = (q p.1.succ).1))) ) := by
  classical
  intro q a Q A q' sigma cov e hparent i s p hidx
  calc
    (q' i.succ).1 = (q' (sigma p.1).succ).1 := by rw [hidx]
    _ = (A a (q p.1.succ)).1 := by rw [hparent]
    _ = (q p.1.succ).1 := cov.1 _

private theorem hchildCurvPos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
              ∀ (i : Fin (3 : ℕ)),
                ∀ (s : Bool),
                  let p := e.symm (i, s)
                  ¬(q p.1.succ).1 = (0 : ℤ) → 0 < (q p.1.succ).1
    ) := by
  classical
  intro q hq e i s p hz
  have hn := (ProperBandCurvatureStructure q hq).2.1 p.1
  omega

private theorem hout :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (U : ProtoTile), ∀ (a : BandPackingSymmetry),
        let P := BandPackingSymmetryPartialOdometerAction
        (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction a h) = Option.map
            (BandPackingSymmetrySlopeAction a U) (PartialOdometerSlope h)) → (∀ (p₀ : ℝ × ℝ),
            (PartialOdometerSlope h = some p₀) → (PartialOdometerSlope (P a h) = some
            (BandPackingSymmetrySlopeAction a U p₀))) ) := by
  classical
  intro h U a P houterSlope p₀ hp₀
  rw [houterSlope, hp₀]
  rfl

private theorem hchild :
    (by
      classical
      exact
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs : Fin (3 : ℕ) → Bool → PartialOdometer), ∀
            (a : BandPackingSymmetry),
        let P := BandPackingSymmetryPartialOdometerAction
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction a (hs p.1 p.2)) =
            Option.map (BandPackingSymmetrySlopeAction a (S p.1 p.2)) (PartialOdometerSlope (hs
            p.1 p.2))) → (∀ (pᵢ : ℝ × ℝ), (PartialOdometerSlope (hs p.1 p.2) = some pᵢ) →
            (PartialOdometerSlope (P a (hs p.1 p.2)) = some (BandPackingSymmetrySlopeAction a (S
            p.1 p.2) pᵢ))) ) := by
  classical
  intro S hs a P e i s p hchildSlope pᵢ hpᵢ
  rw [hchildSlope, hpᵢ]
  rfl

private theorem hvecTarget :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let q' := Q a q
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (negative : Bool), (∀ (i : Fin (3 : ℕ)),
        let e := if negative = true then (-1 : GaussianInt) else (1 : GaussianInt);
        let incoming := BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))));
        let cyclic := BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q (i + (2 : Fin (3
            : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ), BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)); BandVectors.2
            (BandPackingSymmetryQuadrupleAction a q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation a = true then -i else i) i).succ)
            (BandPackingSymmetryQuadrupleAction a q (0 : Fin (4 : ℕ))) = e * incoming.2 ∧
            BandVectors.2 (BandPackingSymmetryQuadrupleAction a q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation a = true then -i else i) i + (2 : Fin (3 :
            ℕ))).succ) (BandPackingSymmetryQuadrupleAction a q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation a = true then -i else i) i + (1 : Fin (3 :
            ℕ))).succ) = e * if BandPackingSymmetryReversesOrientation a = true then
            -GaussianQuarterTurn cyclic.2 else cyclic.2) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        (sigma p.1 + 2 = i + 2) → ((sigma p.1 + 1 = i + 1) → (BandVectors.2 (q' ((i + 2).succ))
            (q' ((i + 1).succ)) = (if negative then (-1 : GaussianInt) else 1) * (if
            BandPackingSymmetryReversesOrientation a then -GaussianQuarterTurn
            (BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1
            + 1).succ)), BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))).2 else
            (BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1
            + 1).succ)), BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))).2)))) ) := by
  classical
  intro q a Q q' sigma e negative hvecAffine i s p hidx2 hidx1
  have hv := (hvecAffine p.1).2
  change BandVectors.2 (Q a q ((i + 2).succ)) (Q a q ((i + 1).succ)) = _
  rw [← hidx2, ← hidx1]
  exact hv

private theorem hsign :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry),
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        ∀ (delta : Bool), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (negative : Bool),
            (negative = delta) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        ((sigma p.1, xor p.2 delta) = (i, s)) → ((if s = true then (1 : ℝ) else -1) = (if p.2 =
            true then (1 : ℝ) else -1) * (if negative then (-1 : ℝ) else 1))) ) := by
  classical
  intro a sigma delta e negative hphaseEq i s p hpair
  have hb := congrArg Prod.snd hpair
  rw [← hphaseEq] at hb
  cases hp : p.2 <;> cases hn : negative
  all_goals
    have hb' : s = xor p.2 negative := by
      simpa [hp, hn] using hb.symm
    simp [hp, hn, hb']

private theorem hc1At1079 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool),
        let p := e.symm (i, s)
        (TileCentroid (S p.1 p.2) - TileCentroid U = (if p.2 = true then (1 : ℝ) else (-1 : ℝ)) •
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q
            (p.1 + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (p.1 + (2 :
            Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 :
            ℕ))).succ))).1))) → ((TileCentroid (S p.1 p.2)).1 - (TileCentroid U).1 = (if p.2 =
            true then (1 : ℝ) else -1) * (((GaussianInt.toComplex (BandVectors.1 (q ((p.1 +
            2).succ)) (q ((p.1 + 1).succ)))).re + (GaussianInt.toComplex (BandVectors.1 (q ((p.1
            + 2).succ)) (q ((p.1 + 1).succ)))).im) / 2)) ) := by
  classical
  intro U q S e i s p hc
  have h := congrArg Prod.fst hc
  cases hp : p.2 <;> simp [hp, GaussianRealPoint, smul_eq_mul] at h ⊢
  · ring_nf at h ⊢; exact h
  · ring_nf at h ⊢; exact h

private theorem hc2At1089 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool),
        let p := e.symm (i, s)
        (TileCentroid (S p.1 p.2) - TileCentroid U = (if p.2 = true then (1 : ℝ) else (-1 : ℝ)) •
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q
            (p.1 + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (p.1 + (2 :
            Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 :
            ℕ))).succ))).1))) → ((TileCentroid (S p.1 p.2)).2 - (TileCentroid U).2 = (if p.2 =
            true then (1 : ℝ) else -1) * (((GaussianInt.toComplex (BandVectors.1 (q ((p.1 +
            2).succ)) (q ((p.1 + 1).succ)))).im - (GaussianInt.toComplex (BandVectors.1 (q ((p.1
            + 2).succ)) (q ((p.1 + 1).succ)))).re) / 2)) ) := by
  classical
  intro U q S e i s p hc
  have h := congrArg Prod.snd hc
  cases hp : p.2 <;> simp [hp, GaussianRealPoint, smul_eq_mul] at h ⊢
  · ring_nf at h ⊢; exact h
  · ring_nf at h ⊢; exact h

private theorem hcentMix :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool),
        let p := e.symm (i, s)
        (TileCentroid (S p.1 p.2) - TileCentroid U = (if p.2 = true then (1 : ℝ) else (-1 : ℝ)) •
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q
            (p.1 + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1 (q (p.1 + (2 :
            Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 :
            ℕ))).succ))).1))) → (
        let v0 := BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let vmix := v0 - GaussianQuarterTurn v0
        let scale : ℝ := (if p.2 = true then (1 : ℝ) else -1) * (1 / 2)
        TileCentroid (S p.1 p.2) - TileCentroid U = scale • GaussianRealPoint vmix) ) := by
  classical
  intro U q S e i s p hc v0 vmix scale
  cases hp : p.2 <;>
    simpa [v0, vmix, scale, GaussianRealPoint, GaussianQuarterTurn,
      smul_eq_mul, hp] using hc

private theorem hslopeMix :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool),
            ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ : ℝ × ℝ), (pᵢ.1 - p₀.1 = (if p.2 = true then (1 : ℝ) else (-1 : ℝ))
            * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q (p.1 + (1 :
            Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (p.1 + (2 : Fin (3 : ℕ))).succ) (q
            (p.1 + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((pᵢ.2 - p₀.2 = (if p.2 = true then (1 :
            ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (p.1 + (2 : Fin (3 :
            ℕ))).succ) (q (p.1 + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (p.1 +
            (2 : Fin (3 : ℕ))).succ) (q (p.1 + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (
        let u0 := BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let umix := u0 + GaussianQuarterTurn u0
        let scale : ℝ := (if p.2 = true then (1 : ℝ) else -1) * (1 / 2)
        pᵢ - p₀ = scale • GaussianRealPoint umix)) ) := by
  classical
  intro q e i s p p₀ pᵢ hdx hdy u0 umix scale
  apply Prod.ext
  · cases hp : p.2
    · have hh := hdx
      rw [GaussianInt.intCast_re
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))),
        GaussianInt.intCast_im
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))] at hh
      simp only [hp, Bool.false_eq_true, ↓reduceIte, one_div, neg_mul, one_mul, Fin.isValue,
          Prod.fst_sub, ite_mul, GaussianRealPoint, Int.reduceNeg, GaussianQuarterTurn,
          Zsqrtd.re_add, Int.cast_add, GaussianInt.intCast_re, Int.cast_neg,
          GaussianInt.intCast_im, Zsqrtd.im_add, neg_smul, Prod.smul_mk, smul_eq_mul,
          Prod.neg_mk, scale, umix, u0] at hh ⊢
      exact hh
    · have hh := hdx
      rw [GaussianInt.intCast_re
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))),
        GaussianInt.intCast_im
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))] at hh
      simp only [hp, ↓reduceIte, one_div, one_mul, Fin.isValue, Prod.fst_sub, ite_mul,
          GaussianRealPoint, Int.reduceNeg, GaussianQuarterTurn, Zsqrtd.re_add, Int.cast_add,
          GaussianInt.intCast_re, Int.cast_neg, GaussianInt.intCast_im, Zsqrtd.im_add,
          Prod.smul_mk, smul_eq_mul, scale, umix, u0] at hh ⊢
      exact hh
  · cases hp : p.2
    · have hh := hdy
      rw [GaussianInt.intCast_re
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))),
        GaussianInt.intCast_im
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))] at hh
      simp only [hp, Bool.false_eq_true, ↓reduceIte, one_div, neg_mul, one_mul, Fin.isValue,
          Prod.snd_sub, ite_mul, GaussianRealPoint, Int.reduceNeg, GaussianQuarterTurn,
          Zsqrtd.re_add, Int.cast_add, GaussianInt.intCast_re, Int.cast_neg,
          GaussianInt.intCast_im, Zsqrtd.im_add, neg_smul, Prod.smul_mk, smul_eq_mul,
          Prod.neg_mk, scale, umix, u0] at hh ⊢
      exact hh
    · have hh := hdy
      rw [GaussianInt.intCast_re
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))),
        GaussianInt.intCast_im
        (BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ)))] at hh
      simp only [hp, ↓reduceIte, one_div, one_mul, Fin.isValue, Prod.snd_sub, ite_mul,
          GaussianRealPoint, Int.reduceNeg, GaussianQuarterTurn, Zsqrtd.re_add, Int.cast_add,
          GaussianInt.intCast_re, Int.cast_neg, GaussianInt.intCast_im, Zsqrtd.im_add,
          Prod.smul_mk, smul_eq_mul, scale, umix, u0] at hh ⊢
      exact hh

private theorem hmix' :
    (by
      classical
      exact
        let symmetryMix : Bool → GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun r z => if r then
            (z.1 + GaussianQuarterTurn z.1, z.2 - GaussianQuarterTurn z.2)
          else (z.1 - GaussianQuarterTurn z.1, z.2 + GaussianQuarterTurn z.2)
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry), ∀ (e : Fin (3 : ℕ)
            × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        let v0 := BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let u0 := BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        ((BandPackingSymmetryAffineVectorAction a (symmetryMix false (v0, u0))).2 = (symmetryMix
            (false ^^ BandPackingSymmetryReversesOrientation a)
            (BandPackingSymmetryAffineVectorAction a (v0, u0))).2) →
            ((BandPackingSymmetryAffineVectorAction a (symmetryMix false (v0, u0))).2 = (if
            BandPackingSymmetryReversesOrientation a then (BandPackingSymmetryAffineVectorAction
            a (v0, u0)).2 - GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction a (v0,
            u0)).2 else (BandPackingSymmetryAffineVectorAction a (v0, u0)).2 +
            GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction a (v0, u0)).2)) ) := by
  classical
  intro symmetryMix q a e i s p v0 u0 hmix
  cases hr : BandPackingSymmetryReversesOrientation a <;>
    simpa [symmetryMix, hr] using hmix

private theorem hsum :
    (by
      classical
      exact
        let symmetryMix : Bool → GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun r z => if r then
            (z.1 + GaussianQuarterTurn z.1, z.2 - GaussianQuarterTurn z.2)
          else (z.1 - GaussianQuarterTurn z.1, z.2 + GaussianQuarterTurn z.2)
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let q' := Q a q
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (negative : Bool), ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ)) = (if negative then (-1 :
            GaussianInt) else 1) * (if BandPackingSymmetryReversesOrientation a then
            -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q ((p.1
            + 2).succ)) (q ((p.1 + 1).succ)), BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 +
            1).succ)))).2 else (BandPackingSymmetryAffineVectorAction a (BandVectors.1 (q ((p.1 +
            2).succ)) (q ((p.1 + 1).succ)), BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 +
            1).succ)))).2)) → (
        let v0 := BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let u0 := BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        ((BandPackingSymmetryAffineVectorAction a (symmetryMix false (v0, u0))).2 = (if
            BandPackingSymmetryReversesOrientation a then (BandPackingSymmetryAffineVectorAction
            a (v0, u0)).2 - GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction a (v0,
            u0)).2 else (BandPackingSymmetryAffineVectorAction a (v0, u0)).2 +
            GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction a (v0, u0)).2)) →
            (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ)) + GaussianQuarterTurn
            (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))) = (if negative then (-1 :
            GaussianInt) else 1) * (BandPackingSymmetryAffineVectorAction a (symmetryMix false
            (v0, u0))).2)) ) := by
  classical
  intro symmetryMix q a Q q' e negative i s p hvecTarget v0 u0 hmix'
  rw [hvecTarget, hmix']
  cases hn : negative <;>
    cases hr : BandPackingSymmetryReversesOrientation a <;>
    ext <;> simp [GaussianQuarterTurn] <;> try ring

private theorem hslopeCov :
    (by
      classical
      exact
        let symmetryMix : Bool → GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun r z => if r then
            (z.1 + GaussianQuarterTurn z.1, z.2 - GaussianQuarterTurn z.2)
          else (z.1 - GaussianQuarterTurn z.1, z.2 + GaussianQuarterTurn z.2)
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let q' := Q a q
        ∀ (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool), ∀ (negative : Bool), ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool),
        let p := e.symm (i, s)
        ∀ (p₀ : ℝ × ℝ), ∀ (pᵢ : ℝ × ℝ), ((if s = true then (1 : ℝ) else -1) = (if p.2 = true then
            (1 : ℝ) else -1) * (if negative then (-1 : ℝ) else 1)) → (
        let v0 := BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let u0 := BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
        let vmix := v0 - GaussianQuarterTurn v0
        let umix := u0 + GaussianQuarterTurn u0
        let scale : ℝ := (if p.2 = true then (1 : ℝ) else -1) * (1 / 2)
        (TileCentroid (BandPackingSymmetryTileAction a (S p.1 p.2)) - TileCentroid
            (BandPackingSymmetryTileAction a U) = scale • GaussianRealPoint
            (BandPackingSymmetryAffineVectorAction a (vmix, umix)).1 ∧
            BandPackingSymmetrySlopeAction a (S p.1 p.2) pᵢ - BandPackingSymmetrySlopeAction a U
            p₀ = scale • GaussianRealPoint (BandPackingSymmetryAffineVectorAction a (vmix,
            umix)).2) → ((BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ)) +
            GaussianQuarterTurn (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))) = (if
            negative then (-1 : GaussianInt) else 1) * (BandPackingSymmetryAffineVectorAction a
            (symmetryMix false (v0, u0))).2) → (BandPackingSymmetrySlopeAction a (S p.1 p.2) pᵢ -
            BandPackingSymmetrySlopeAction a U p₀ = ((if s = true then (1 : ℝ) else -1) * (1 /
            2)) • GaussianRealPoint (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ)) +
            GaussianQuarterTurn (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ))))))) ) := by
  classical
  intro symmetryMix U q S a Q q' e negative i s p p₀ pᵢ hsign v0 u0 vmix umix scale
      hdiffTransport hsum
  calc
    _ = scale • GaussianRealPoint
        (BandPackingSymmetryAffineVectorAction a
          (symmetryMix false (v0, u0))).2 := hdiffTransport.2
    _ = _ := by
      rw [hsum]
      cases hp : p.2 <;> cases hn : negative <;> cases hs' : s
      all_goals
        simp [hp, hn, hs'] at hsign
      all_goals norm_num at hsign
      all_goals simp [scale, hp,
        GaussianRealPoint, smul_eq_mul]

end TileOdometerSymmetryProof

namespace TileOdometerAssembly

private theorem hcentroid' :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (a : BandPackingSymmetry),
        let Q := BandPackingSymmetryQuadrupleAction
        let B := BandPackingSymmetryTileAction
        let q' := Q a q
        ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction a q)
            (BandPackingSymmetryTileAction a U) i s (S' i s)) → (∀ i, ∀ s, TileCentroid (S' i s)
            - TileCentroid (B a U) = (if s = true then (1 : Real) else -1) • ((1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ))) -
            (-((GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)))).2),
            (GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)))).1)))) )
            := by
  classical
  intro U q a Q B q' S' hocc'
  exact fun i s => (hocc' i s).2.2

private theorem hphaseEq :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (∀ (a :
            BandPackingSymmetry), ∀ (delta : Bool), (BandPackingSymmetryScopedPhase a q delta) →
            (∀ (negative : Bool), (BandPackingSymmetryScopedPhase a q negative) → (negative =
            delta))) ) := by
  classical
  intro q hq a delta hphase negative hphaseAffine
  exact BandPackingSymmetryScopedPhaseUnique a q hq negative delta
      hphaseAffine hphase

end TileOdometerAssembly

namespace UnitOdometerSymmetry

private theorem unitSymmetry :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (D : CircleCoordinates), (BandPackingSymmetryCircleAction
            a D).1 = D.1) → ((∀ (D : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k :
            PartialOdometer), D.1 = (1 : ℤ) → TileOdometer D U k → ∃ (z : GaussianInt) (x :
            LatticeCell), D = ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z) ∧ U.cells =
            {x} ∧ (↑k.domain : Set GaussianInt) = FootprintVertices U ∧ OdometerTranslation k
            (CurvatureOneOdometer z)) → (∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (z :
            GaussianInt), ∀ (x : GaussianInt), (U.cells = {x}) → (((↑k.domain : Set GaussianInt)
            = FootprintVertices U) → ((OdometerTranslation k (CurvatureOneOdometer z)) → (∀ a :
            BandPackingSymmetry, TileOdometer (BandPackingSymmetryCircleAction a (1, 1 + 2 * z))
            (BandPackingSymmetryTileAction a U) (BandPackingSymmetryPartialOdometerAction a
            k)))))) ) := by
  classical
  intro circleCurvature extractUnit U k z x hU hdom htrans a
  induction a generalizing z x U k hU hdom htrans with
  | identity =>
      simpa [BandPackingSymmetryCircleAction,
        BandPackingSymmetryTileAction,
        BandPackingSymmetryPartialOdometerAction] using
        TileOdometer.unit z x U k hU hdom htrans
  | shift w =>
      rcases w with ⟨wr, wi⟩
      have triangular := TileOdometerSymmetryProof.triangular
      have shiftDx := TileOdometerSymmetryProof.shiftDx wr wi triangular
      have shiftDy := TileOdometerSymmetryProof.shiftDy wr wi triangular
      rcases htrans with ⟨v, a0, b0, hvdom, hvval⟩
      let d1 := BandPackingShiftPotential ⟨wr, wi⟩ (v + 1) -
        BandPackingShiftPotential ⟨wr, wi⟩ v
      let d2 := BandPackingShiftPotential ⟨wr, wi⟩ (v + ⟨0, 1⟩) -
        BandPackingShiftPotential ⟨wr, wi⟩ v
      let d : GaussianInt := ⟨d1, d2⟩
      let b1 := b0 + BandPackingShiftPotential ⟨wr, wi⟩ v -
        d.re * v.re - d.im * v.im
      have hcorner := TileOdometerSymmetryProof.hcorner wr wi shiftDx shiftDy v
      have hpsi := TileOdometerSymmetryProof.hpsi z wr wi v hcorner
      have hcurv (r : GaussianInt) (hr :
          r ∈ (CurvatureOneOdometer z).domain) :
          (CurvatureOneOdometer (z + ⟨wr, wi⟩)).value r =
            (CurvatureOneOdometer z).value r + wi * r.re * r.im :=
                TileOdometerSymmetryProof.hcurvAt595 z wr wi r hr
      have hC : BandPackingSymmetryCircleAction (.shift ⟨wr, wi⟩)
          (1, 1 + 2 * z) = (1, 1 + 2 * (z + ⟨wr, wi⟩)) := TileOdometerSymmetryProof.hCAt611 z
              wr wi
      rw [hC]
      simp only [BandPackingSymmetryTileAction]
      refine TileOdometer.unit (z + ⟨wr, wi⟩) x U
        (BandPackingSymmetryPartialOdometerAction (.shift ⟨wr, wi⟩) k)
        ?_ ?_ ?_
      · exact hU
      · simpa [BandPackingSymmetryTileAction,
          BandPackingSymmetryPartialOdometerAction] using hdom
      · refine ⟨v, a0 + d, b1, ?_, ?_⟩
        · intro y
          change y ∈ k.domain ↔
            y - v ∈ (CurvatureOneOdometer (z + ⟨wr, wi⟩)).domain
          rw [hvdom]
          simp [CurvatureOneOdometer]
        · intro y hy
          have hyk := TileOdometerSymmetryProof.hyk k wr wi y hy
          have hr : y - v ∈ (CurvatureOneOdometer z).domain :=
            (hvdom y).mp hyk
          have hval := hvval y hyk
          have hshift := (BandPackingSymmetryPartialOdometerActionFormulas
            (.shift ⟨wr, wi⟩) k k).2.2.1 ⟨wr, wi⟩ y hyk
          rw [hshift, hval]
          rw [hcurv (y - v) hr]
          have hpsi' := hpsi (y - v) hr
          have hvplus : v + (y - v) = y := by abel
          rw [hvplus] at hpsi'
          dsimp [b1, d, d1, d2] at hpsi' ⊢
          linear_combination hpsi'
  | negate =>
      rcases htrans with ⟨v, a0, b0, hvdom, hvval⟩
      let I : GaussianInt := ⟨0, 1⟩
      have hcell : (TileQuarterTurn U).cells =
          {GaussianQuarterTurn x - 1} := TileOdometerSymmetryProof.hcellAt653 U x hU
      have hdomain := TileOdometerSymmetryProof.hdomainAt657 U k hdom
      have hdomainUnit := TileOdometerSymmetryProof.hdomainUnitAt664 z
      have hunitValue := TileOdometerSymmetryProof.hunitValueAt682 z
      have hinverse := TileOdometerSymmetryProof.hinverseAt694 v
      have himage := TileOdometerSymmetryProof.himageAt698 k
      have htrans' := TileOdometerSymmetryProof.htrans'At711 k z v a0 b0 hvdom hvval
          hdomainUnit hunitValue hinverse himage
      have hC : BandPackingSymmetryCircleAction .negate
          (1, 1 + 2 * z) = (1, 1 + 2 * (-z - 1)) := TileOdometerSymmetryProof.hCAt738 z
      rw [hC]
      refine TileOdometer.unit (-z - 1) (GaussianQuarterTurn x - 1)
        (TileQuarterTurn U)
        (BandPackingSymmetryPartialOdometerAction .negate k)
        ?_ hdomain htrans'
      simp [hcell]
  | conjugate =>
      rcases htrans with ⟨v, a0, b0, hvdom, hvval⟩
      let I : GaussianInt := ⟨0, 1⟩
      have hcell :
          (BandPackingSymmetryTileAction .conjugate U).cells =
            {-GaussianReflection x - 1} := TileOdometerSymmetryProof.hcellAt753 U x hU
      have hdomain := TileOdometerSymmetryProof.hdomainAt763 U k hdom
      have hdomainUnit := TileOdometerSymmetryProof.hdomainUnitAt787 z
      have hunitValue := TileOdometerSymmetryProof.hunitValueAt805 z
      have hinverse := TileOdometerSymmetryProof.hinverseAt818 v
      have himage := TileOdometerSymmetryProof.himageAt823 k
      have htrans' := TileOdometerSymmetryProof.htrans'At836 k z v a0 b0 hvdom hvval
          hdomainUnit hunitValue hinverse himage
      have hC : BandPackingSymmetryCircleAction .conjugate
          (1, 1 + 2 * z) =
            (1, 1 + 2 * GaussianReflection z) := TileOdometerSymmetryProof.hCAt864 z
      rw [hC]
      refine TileOdometer.unit (GaussianReflection z)
        (-GaussianReflection x - 1)
        (BandPackingSymmetryTileAction .conjugate U)
        (BandPackingSymmetryPartialOdometerAction .conjugate k)
        ?_ hdomain htrans'
      simp [hcell]
  | comp a b iha ihb =>
      have mid := @ihb U k z x hU hdom htrans
      have hcirc := circleCurvature b (1, 1 + 2 * z)
      obtain ⟨z', x', hC, hU', hdom', htrans'⟩ :=
        extractUnit _ _ _ hcirc mid
      change TileOdometer
        (BandPackingSymmetryCircleAction a
          (BandPackingSymmetryCircleAction b (1, 1 + 2 * z)))
        (BandPackingSymmetryTileAction a
          (BandPackingSymmetryTileAction b U))
        (BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b k))
      rw [hC]
      exact @iha _ _ z' x' hU' hdom' htrans'

end UnitOdometerSymmetry

theorem BandPackingSymmetryTileOdometerCovariance
    (g : BandPackingSymmetry) (C : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (hO : TileOdometer C T h) :
    TileOdometer (BandPackingSymmetryCircleAction g C)
      (BandPackingSymmetryTileAction g T)
      (BandPackingSymmetryPartialOdometerAction g h) ∧
    (((BandPackingSymmetryPartialOdometerAction g h).domain :
        Set GaussianInt) =
      BandPackingSymmetryVectorAction g '' (h.domain : Set GaussianInt)) ∧
    (T.cells.Nonempty →
      PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) =
        (PartialOdometerSlope h).map
          (BandPackingSymmetrySlopeAction g T)) := by
-- BODY
  classical
  have domain := (BandPackingSymmetryPartialOdometerActionFormulas g h h).1
  have positiveCells := BandPrototileNonempty.positive
  have odoPositiveCurvature := TileOdometerSymmetryProof.odoPositiveCurvature
  have slopeCov := TileOdometerSymmetryProof.slopeCov g odoPositiveCurvature
  have slope := slopeCov C T h hO
  have lineCircle := TileOdometerSymmetryProof.lineCircle
  have tileEmpty := TileOdometerSymmetryProof.tileEmpty
  have zeroLine := TileOdometerSymmetryProof.zeroLine
  have actionForward := TileOdometerSymmetryProof.actionForward
  have actionDiff := TileOdometerSymmetryProof.actionDiff actionForward
  have lineCov := TileOdometerSymmetryProof.lineCov lineCircle tileEmpty zeroLine
  have circleCurvature := TileOdometerSymmetryProof.circleCurvature
  have extractUnit := TileOdometerSymmetryProof.extractUnit
  have affineMix := TileOdometerSymmetryProof.affineMix
  have transform : ∀ (D : CircleCoordinates) (U : ProtoTile) (k : PartialOdometer),
      TileOdometer D U k → ∀ a : BandPackingSymmetry,
      TileOdometer (BandPackingSymmetryCircleAction a D)
        (BandPackingSymmetryTileAction a U)
        (BandPackingSymmetryPartialOdometerAction a k) := by
    intro D U k ho
    induction ho with
    | line w x hw k hk => intro a; exact lineCov w x hw k hk a
    | unit z x U k hU hdom htrans =>
        have unitSymmetry : ∀ a : BandPackingSymmetry,
            TileOdometer (BandPackingSymmetryCircleAction a (1, 1 + 2 * z))
              (BandPackingSymmetryTileAction a U)
              (BandPackingSymmetryPartialOdometerAction a k) := UnitOdometerSymmetry.unitSymmetry
                  circleCurvature extractUnit U k z x hU hdom htrans
        exact unitSymmetry
    | @decompose q hq S U hs h hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
        intro a
        let Q := BandPackingSymmetryQuadrupleAction
        let B := BandPackingSymmetryTileAction
        let P := BandPackingSymmetryPartialOdometerAction
        let q' := Q a q
        let sigma : Fin 3 → Fin 3 := fun i =>
          if BandPackingSymmetryReversesOrientation a then -i else i
        have hocc := TileOdometerSymmetryProof.hocc U q S hs hsub hfoot hcentroid
        have cov := BandPackingSymmetryCovariance a
        obtain ⟨delta, e, S', hphase, he, hS, hocc', hcells'⟩ :=
          cov.2.2 q U S hq hT hocc hcells
        have hproper' : ProperBandQuadruple q' := by
          simpa [q'] using BandPackingSymmetryProperCovariance a q hq
        have hneg1 : -(1 : Fin 3) = 2 := rfl
        have hneg2 : -(2 : Fin 3) = 1 := rfl
        have hparent := TileOdometerSymmetryProof.hparentAt910 q a hneg1 hneg2
        have hT' := TileOdometerSymmetryProof.hT' U q hT a cov
        let hs' : Fin 3 → Bool → PartialOdometer := fun j s =>
          P a (hs (e.symm (j, s)).1 (e.symm (j, s)).2)
        have hsub' := TileOdometerSymmetryProof.hsub' q S hs ih a delta e S' he hS hparent
        have hdom' := TileOdometerSymmetryProof.hdom' h hs hdom a e
        have hvalue' := TileOdometerSymmetryProof.hvalue' h actionDiff hs hdom hvalue a e
        have hcompat' := TileOdometerSymmetryProof.hcompat' hs hcompat a e
        have hfoot' : ∀ i s, FootprintVertices (S' i s) ⊆
            FootprintVertices (B a U) := fun i s => (hocc' i s).2.1
        have hcentroid' := TileOdometerAssembly.hcentroid' U q a S' hocc'
        obtain ⟨negative, hphaseAffine, hvecAffine⟩ :=
          BandPackingSymmetryAffineVectorCovariance a q hq
        have hphaseEq := TileOdometerAssembly.hphaseEq q hq a delta hphase negative hphaseAffine
        have hUne : U.cells.Nonempty :=
          positiveCells (q 0) U (ProperBandCurvatureStructure q hq).1 hT
        have hOorig := TileOdometer.decompose hq hT hsub hcells hfoot hcentroid
            hdom hvalue hcompat hslope
        have hUdom := PositiveCurvatureTileOdometerDomain (q 0) U h
          (ProperBandCurvatureStructure q hq).1 hOorig
        have houterSlope := BandPrototileFootprintSlopeCovariance a (q 0) U h
          hT hUne hUdom
        refine TileOdometer.decompose hproper' hT' hsub' hcells' hfoot' hcentroid'
          hdom' hvalue' hcompat' ?_
        intro i s
        let p := e.symm (i, s)
        have hep : e p = (i, s) := e.apply_symm_apply (i, s)
        have hpair := TileOdometerSymmetryProof.hpairAt1015 a delta e he i s hep
        have hidx : sigma p.1 = i := congrArg Prod.fst hpair
        have hcurv : (q' i.succ).1 = (q p.1.succ).1 := TileOdometerSymmetryProof.hcurvAt1021 q a
            cov e hparent i s hidx
        have hprotoChild := TileOdometerBandPrototile (q p.1.succ)
          (S p.1 p.2) (hs p.1 p.2) (hsub p.1 p.2)
        by_cases hz : (q p.1.succ).1 = 0
        · left
          rw [hcurv, hz]
        · have hchildCurvPos := TileOdometerSymmetryProof.hchildCurvPos q hq e i s hz
          have hchildNe : (S p.1 p.2).cells.Nonempty :=
            positiveCells (q p.1.succ) (S p.1 p.2) hchildCurvPos hprotoChild
          have hchildDom := PositiveCurvatureTileOdometerDomain (q p.1.succ)
            (S p.1 p.2) (hs p.1 p.2) hchildCurvPos (hsub p.1 p.2)
          have hchildSlope := BandPrototileFootprintSlopeCovariance a
            (q p.1.succ) (S p.1 p.2) (hs p.1 p.2) hprotoChild hchildNe hchildDom
          rcases hslope p.1 p.2 with hzero | ⟨p₀, pᵢ, hp₀, hpᵢ, hdx, hdy⟩
          · omega
          · have hout : PartialOdometerSlope (P a h) =
                some (BandPackingSymmetrySlopeAction a U p₀) := TileOdometerSymmetryProof.hout h U a
                    houterSlope p₀ hp₀
            have hchild : PartialOdometerSlope (P a (hs p.1 p.2)) =
                some (BandPackingSymmetrySlopeAction a (S p.1 p.2) pᵢ) :=
                    TileOdometerSymmetryProof.hchild S hs a e i s hchildSlope pᵢ hpᵢ
            have hidx2 : sigma p.1 + 2 = i + 2 := congrArg (fun j : Fin 3 => j + 2) hidx
            have hidx1 : sigma p.1 + 1 = i + 1 := congrArg (fun j : Fin 3 => j + 1) hidx
            have hvecTarget := TileOdometerSymmetryProof.hvecTarget q a e negative hvecAffine i s
                hidx2 hidx1
            have hsign := TileOdometerSymmetryProof.hsign a delta e negative hphaseEq i s hpair
            have hc := hcentroid p.1 p.2
            have hc1 := TileOdometerSymmetryProof.hc1At1079 U q S e i s hc
            have hc2 := TileOdometerSymmetryProof.hc2At1089 U q S e i s hc
            let v0 := BandVectors.1 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
            let u0 := BandVectors.2 (q ((p.1 + 2).succ)) (q ((p.1 + 1).succ))
            let vmix := v0 - GaussianQuarterTurn v0
            let umix := u0 + GaussianQuarterTurn u0
            let scale : ℝ := (if p.2 = true then (1 : ℝ) else -1) * (1 / 2)
            have hcentMix := TileOdometerSymmetryProof.hcentMix U q S e i s hc
            have hslopeMix := TileOdometerSymmetryProof.hslopeMix q e i s p₀ pᵢ hdx hdy
            have hdiffTransport := P5625T1CentroidSlopeDifferenceCovariance.2 a U (S p.1 p.2)
              pᵢ p₀ vmix umix scale hcentMix hslopeMix
            have hmix := congrArg Prod.snd (affineMix a false (v0, u0))
            have hmix' := TileOdometerSymmetryProof.hmix' q a e i s hmix
            have hsum := TileOdometerSymmetryProof.hsum q a e negative i s hvecTarget hmix'
            have hslopeCov :
                BandPackingSymmetrySlopeAction a (S p.1 p.2) pᵢ -
                    BandPackingSymmetrySlopeAction a U p₀ =
                  ((if s = true then (1 : ℝ) else -1) * (1 / 2)) •
                    GaussianRealPoint
                      (BandVectors.2 (q' ((i + 2).succ)) (q' ((i + 1).succ)) +
                        GaussianQuarterTurn
                          (BandVectors.2 (q' ((i + 2).succ))
                            (q' ((i + 1).succ)))) := TileOdometerSymmetryProof.hslopeCov U q S a e
                                negative i s p₀ pᵢ hsign hdiffTransport hsum
            refine Or.inr ⟨BandPackingSymmetrySlopeAction a U p₀,
              BandPackingSymmetrySlopeAction a (S p.1 p.2) pᵢ, ?_, ?_, ?_, ?_⟩
            · simpa [hs'] using hout
            · simpa [hs'] using hchild
            · cases s <;>
                simpa [BandPackingSymmetrySlopeAction, GaussianRealPoint,
                  GaussianQuarterTurn, GaussianInt.intCast_re,
                  GaussianInt.intCast_im, smul_eq_mul, sub_eq_add_neg] using
                    congrArg Prod.fst hslopeCov
            · cases s <;>
                simpa [BandPackingSymmetrySlopeAction, GaussianRealPoint,
                  GaussianQuarterTurn, GaussianInt.intCast_re,
                  GaussianInt.intCast_im, smul_eq_mul] using
                    congrArg Prod.snd hslopeCov
  refine ⟨?_, domain, slope⟩
  · exact transform C T h hO g

end ApollonianSuperharmonic

end
