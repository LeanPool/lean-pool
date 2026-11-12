/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProjectiveVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhaseUnique
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction

-- [TABLET NODE: BandPackingSymmetryInversePhaseCancellation]

/-!
# BandPackingSymmetryInversePhaseCancellation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InversePhaseProof

private theorem composition :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (b : BandPackingSymmetry), ∀ (q : Fin 4 ->
            CircleCoordinates), BandPackingSymmetryQuadrupleAction (.comp a b) q =
            BandPackingSymmetryQuadrupleAction a (BandPackingSymmetryQuadrupleAction b q) ) := by
  classical
  intro a b q
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  cases ha : BandPackingSymmetryReversesOrientation a <;>
    cases hb : BandPackingSymmetryReversesOrientation b <;>
    funext k <;> fin_cases k <;>
    simp [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
      BandPackingSymmetryReversesOrientation, ha, hb, neg1, neg2]

private theorem phaseComposition :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (b : BandPackingSymmetry), ∀ (q : Fin 4 ->
            CircleCoordinates), BandPackingSymmetryQuadrupleAction (.comp a b) q =
            BandPackingSymmetryQuadrupleAction a (BandPackingSymmetryQuadrupleAction b q)) →
            (forall (a b : BandPackingSymmetry) (q : Fin 4 -> CircleCoordinates) (deltaB deltaA :
            Bool), ProperBandQuadruple q -> BandPackingSymmetryScopedPhase b q deltaB ->
            BandPackingSymmetryScopedPhase a (BandPackingSymmetryQuadrupleAction b q) deltaA ->
            BandPackingSymmetryScopedPhase (.comp a b) q (xor deltaB deltaA)) ) := by
  classical
  intro composition
  have qneg (v : GaussianInt) : GaussianQuarterTurn (-v) = -GaussianQuarterTurn v := by
    ext <;> simp [GaussianQuarterTurn]
  have qtwo (v : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn v) = -v := by
    ext <;> simp [GaussianQuarterTurn]
  have vneg (g : BandPackingSymmetry) (v : GaussianInt) :
      BandPackingSymmetryVectorAction g (-v) = -BandPackingSymmetryVectorAction g v := by
    induction g generalizing v with
    | identity => rfl
    | negate => exact qneg v
    | conjugate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
    | shift w => rfl
    | comp a b ia ib => simp only [BandPackingSymmetryVectorAction, ib, ia]
  have vquarter (g : BandPackingSymmetry) (v : GaussianInt) :
      BandPackingSymmetryVectorAction g (GaussianQuarterTurn v) =
        if BandPackingSymmetryReversesOrientation g then
          -GaussianQuarterTurn (BandPackingSymmetryVectorAction g v)
        else GaussianQuarterTurn (BandPackingSymmetryVectorAction g v) := by
    induction g generalizing v with
    | identity => rfl
    | negate => rfl
    | conjugate =>
        ext <;> simp [BandPackingSymmetryVectorAction,
          BandPackingSymmetryReversesOrientation, GaussianQuarterTurn, GaussianReflection]
    | shift w => rfl
    | comp a b ia ib =>
        cases ha : BandPackingSymmetryReversesOrientation a <;>
          cases hb : BandPackingSymmetryReversesOrientation b <;>
          simp [BandPackingSymmetryVectorAction, BandPackingSymmetryReversesOrientation,
            ib, ia, ha, hb, vneg]
  intro a b q db da hq hb ha i
  have hbi := hb i
  have hai := ha (if BandPackingSymmetryReversesOrientation b then -i else i)
  change _ = _ ∧ _ = _ ∧ _ = _ at hbi hai
  cases ra : BandPackingSymmetryReversesOrientation a <;>
    cases rb : BandPackingSymmetryReversesOrientation b <;>
    cases db <;> cases da <;> fin_cases i
  all_goals
    simp only [rb, Bool.false_eq_true, ↓reduceIte, Fin.mk_one, Fin.isValue,
        Fin.succ_one_eq_two, neg_mul, one_mul, Fin.reduceAdd, Fin.succ_zero_eq_one,
        Fin.reduceSucc, ra, BandPackingSymmetryReversesOrientation, bne_self_eq_false,
        Bool.bne_false, mul_neg, neg_add_cancel, neg_neg, Bool.bne_true, Bool.not_false,
        Fin.reduceFinMk, Fin.zero_eta, zero_add, neg_zero] at hbi hai ⊢
    simp only [composition]
    rcases hbi with ⟨bin, brev, bcyc⟩
    rcases hai with ⟨ain, arev, acyc⟩
    rw [ain, arev, acyc, bin, brev, bcyc]
    simp [BandPackingSymmetryVectorAction, vneg, vquarter, ra, qneg, qtwo]

private theorem qfour :
    (by
      classical
      exact
        ∀ (v : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn v))) = v ) := by
  classical
  intro v
  ext <;> simp [GaussianQuarterTurn]

private theorem injN :
    (by
      classical
      exact
        (∀ (v : GaussianInt), -GaussianQuarterTurn (GaussianQuarterTurn v) = v) →
            (Function.Injective GaussianQuarterTurn) ) := by
  classical
  intro invN x y h
  simpa only [invN] using congrArg (fun z => -GaussianQuarterTurn z) h

private theorem injK :
    (by
      classical
      exact
        (∀ (v : GaussianInt), -GaussianReflection (-GaussianReflection v) = v) →
            (Function.Injective (fun v => -GaussianReflection v)) ) := by
  classical
  intro invK x y h
  simpa only [invK] using congrArg (fun z => -GaussianReflection z) h

private theorem domain :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (h : PartialOdometer),
            (BandPackingSymmetryPartialOdometerAction g h).domain = h.domain.image
            (BandPackingSymmetryVectorAction g) ) := by
  classical
  intro g h
  induction g generalizing h with
  | identity => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
  | negate => rfl
  | conjugate => rfl
  | shift w => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
  | comp a b ia ib =>
      simp only [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
      rw [ia, ib, Finset.image_image]
      rfl

private theorem nvalue :
    (by
      classical
      exact
        (∀ (v : GaussianInt), -GaussianQuarterTurn (GaussianQuarterTurn v) = v) →
            ((Function.Injective GaussianQuarterTurn) → (∀ (h : PartialOdometer), ∀ (x :
            GaussianInt), (BandPackingSymmetryPartialOdometerAction .negate h).value
            (GaussianQuarterTurn x) = h.value x)) ) := by
  classical
  intro invN injN h x
  have mem : GaussianQuarterTurn x ∈ h.domain.image GaussianQuarterTurn ↔ x ∈ h.domain := by
    simp [Finset.mem_image, injN.eq_iff]
  by_cases hx : x ∈ h.domain
  · simp only [BandPackingSymmetryPartialOdometerAction, mem, ite_eq_left hx, invN]
  · simp only [BandPackingSymmetryPartialOdometerAction, mem, ite_eq_right hx]
    exact (h.value_outside x hx).symm

private theorem kvalue :
    (by
      classical
      exact
        (∀ (v : GaussianInt), -GaussianReflection (-GaussianReflection v) = v) →
            ((Function.Injective (fun v => -GaussianReflection v)) → (∀ (h : PartialOdometer), ∀
            (x : GaussianInt), (BandPackingSymmetryPartialOdometerAction .conjugate h).value
            (-GaussianReflection x) = h.value x)) ) := by
  classical
  intro invK injK h x
  have mem : -GaussianReflection x ∈ h.domain.image (fun v => -GaussianReflection v) ↔
      x ∈ h.domain := by
    simp [Finset.mem_image, injK.eq_iff]
  by_cases hx : x ∈ h.domain
  · simp only [BandPackingSymmetryPartialOdometerAction, mem, ite_eq_left hx, invK]
  · simp only [BandPackingSymmetryPartialOdometerAction, mem, ite_eq_right hx]
    exact (h.value_outside x hx).symm

private theorem partial_ext :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (k : PartialOdometer), (h.domain = k.domain) → ((∀ x, h.value
            x = k.value x) → (h = k)) ) := by
  classical
  intro h k hd hv
  cases h
  cases k
  dsimp at hd hv
  subst hd
  have he := funext hv
  subst he
  rfl

private theorem tileN :
    (by
      classical
      exact
        (∀ (v : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn v))) = v) → (∀ (T : ProtoTile), TileQuarterTurn (TileQuarterTurn
            (TileQuarterTurn (TileQuarterTurn T))) = T) ) := by
  classical
  intro qfour T
  cases T with
  | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · simp only [TileQuarterTurn, Finset.image_image, Function.comp_def]
        have map : (fun x : GaussianInt =>
            GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
              (GaussianQuarterTurn x - 1) - 1) - 1) - 1) = id := by
          funext x
          ext <;> simp [GaussianQuarterTurn]
        rw [map, Finset.image_id]
      · exact qfour anchor

private theorem tileK :
    (by
      classical
      exact
        ∀ (T : ProtoTile), BandPackingSymmetryTileAction .conjugate
            (BandPackingSymmetryTileAction .conjugate T) = T ) := by
  classical
  intro T
  cases T with
  | mk cells anchor =>
      apply congrArg₂ ProtoTile.mk
      · simp only [BandPackingSymmetryTileAction, TileQuarterTurn, TileReflection,
          Finset.image_image, Function.comp_def]
        have map : (fun x : GaussianInt =>
            GaussianQuarterTurn (GaussianQuarterTurn (GaussianReflection
              (GaussianQuarterTurn (GaussianQuarterTurn
                (GaussianReflection x - ⟨0, 1⟩) - 1) - 1) - ⟨0, 1⟩) - 1) - 1) = id := by
          funext x
          ext <;> simp [GaussianQuarterTurn, GaussianReflection]
        rw [map, Finset.image_id]
      · ext <;> simp [BandPackingSymmetryTileAction, TileQuarterTurn, TileReflection,
          GaussianQuarterTurn, GaussianReflection]

private theorem partialN :
    (by
      classical
      exact
        (∀ (v : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn v))) = v) → ((∀ (g : BandPackingSymmetry), ∀ (h :
                PartialOdometer), (BandPackingSymmetryPartialOdometerAction g h).domain =
            h.domain.image (BandPackingSymmetryVectorAction g)) → ((∀ (h : PartialOdometer), ∀ (x
                : GaussianInt), (BandPackingSymmetryPartialOdometerAction .negate h).value
            (GaussianQuarterTurn x) = h.value x) → ((∀ (h : PartialOdometer), ∀ (k :
                PartialOdometer), (h.domain = k.domain) → ((∀ x, h.value x = k.value x) → (h =
                k))) →
            (∀ (h : PartialOdometer), BandPackingSymmetryPartialOdometerAction .negate
            (BandPackingSymmetryPartialOdometerAction .negate
            (BandPackingSymmetryPartialOdometerAction .negate
            (BandPackingSymmetryPartialOdometerAction .negate h))) = h)))) ) := by
  classical
  intro qfour domain nvalue partial_ext h
  apply partial_ext
  · rw [domain, domain, domain, domain]
    simp only [BandPackingSymmetryVectorAction, Finset.image_image, Function.comp_def]
    have map : (fun x : GaussianInt => GaussianQuarterTurn
        (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x)))) = id :=
      funext qfour
    rw [map, Finset.image_id]
  · intro x
    have he := nvalue
      (BandPackingSymmetryPartialOdometerAction .negate
        (BandPackingSymmetryPartialOdometerAction .negate
          (BandPackingSymmetryPartialOdometerAction .negate h)))
      (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x)))
    rw [qfour, nvalue, nvalue, nvalue] at he
    exact he

private theorem partialK :
    (by
      classical
      exact
        (∀ (v : GaussianInt), -GaussianReflection (-GaussianReflection v) = v) → ((∀ (g :
            BandPackingSymmetry), ∀ (h : PartialOdometer),
            (BandPackingSymmetryPartialOdometerAction g h).domain = h.domain.image
            (BandPackingSymmetryVectorAction g)) → ((∀ (h : PartialOdometer), ∀ (x :
                GaussianInt), (BandPackingSymmetryPartialOdometerAction .conjugate h).value
                (-GaussianReflection x)
            = h.value x) → ((∀ (h : PartialOdometer), ∀ (k : PartialOdometer), (h.domain =
            k.domain) → ((∀ x, h.value x = k.value x) → (h = k))) → (∀ (h : PartialOdometer),
                BandPackingSymmetryPartialOdometerAction .conjugate
            (BandPackingSymmetryPartialOdometerAction .conjugate h) = h)))) ) := by
  classical
  intro invK domain kvalue partial_ext h
  apply partial_ext
  · rw [domain, domain]
    simp only [BandPackingSymmetryVectorAction, Finset.image_image, Function.comp_def]
    have map : (fun x : GaussianInt => -GaussianReflection (-GaussianReflection x)) = id :=
      funext invK
    rw [map, Finset.image_id]
  · intro x
    have he := kvalue (BandPackingSymmetryPartialOdometerAction .conjugate h)
        (-GaussianReflection x)
    rw [invK, kvalue] at he
    exact he

private theorem potential :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (x : GaussianInt), BandPackingShiftPotential (-w) x =
            -BandPackingShiftPotential w x ) := by
  classical
  intro w x
  simp only [BandPackingShiftPotential, Zsqrtd.re_neg, Zsqrtd.im_neg]
  ring

private theorem partialShift :
    (by
      classical
      exact
        (∀ (h : PartialOdometer), ∀ (k : PartialOdometer), (h.domain = k.domain) → ((∀ x, h.value
            x = k.value x) → (h = k))) → ((∀ (w : GaussianInt), ∀ (x : GaussianInt),
            BandPackingShiftPotential (-w) x = -BandPackingShiftPotential w x) → (∀ (w :
            GaussianInt), ∀ (h : PartialOdometer), BandPackingSymmetryPartialOdometerAction
            (.shift (-w)) (BandPackingSymmetryPartialOdometerAction (.shift w) h) = h)) ) := by
  classical
  intro partial_ext potential w h
  apply partial_ext
  · rfl
  · intro x
    by_cases hx : x ∈ h.domain
    · simp [BandPackingSymmetryPartialOdometerAction, hx, potential]
    · simp [BandPackingSymmetryPartialOdometerAction, hx, h.value_outside x hx]

private theorem quadCancel :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (k : BandPackingSymmetry),
            (BandPackingSymmetryReversesOrientation k = BandPackingSymmetryReversesOrientation g)
            → ((∀ C, BandPackingSymmetryCircleAction k (BandPackingSymmetryCircleAction g C) = C)
            → (∀ (q : Fin 4 -> CircleCoordinates), BandPackingSymmetryQuadrupleAction k
            (BandPackingSymmetryQuadrupleAction g q) = q)) ) := by
  classical
  intro g k he hc q
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  cases hg : BandPackingSymmetryReversesOrientation g <;>
    funext i <;> fin_cases i <;>
    simp [BandPackingSymmetryQuadrupleAction, he, hg, hc, neg1, neg2]

private theorem clAt391 :
    (by
      classical
      exact
        let k : BandPackingSymmetry := .comp .negate (.comp .negate .negate)
        ∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction k
            (BandPackingSymmetryCircleAction .negate C) = C ) := by
  classical
  intro k C
  cases C
  simp [k, BandPackingSymmetryCircleAction]

private theorem crAt395 :
    (by
      classical
      exact
        let k : BandPackingSymmetry := .comp .negate (.comp .negate .negate)
        ∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction .negate
            (BandPackingSymmetryCircleAction k C) = C ) := by
  classical
  intro k C
  cases C
  simp [k, BandPackingSymmetryCircleAction]

private theorem clAt408 :
    (by
      classical
      exact
        ∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction .conjugate
            (BandPackingSymmetryCircleAction .conjugate C) = C ) := by
  classical
  intro C
  cases C
  apply Prod.ext
  · rfl
  · ext <;> simp [BandPackingSymmetryCircleAction, GaussianReflection]

private theorem clAt418 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction (.shift
            (-w)) (BandPackingSymmetryCircleAction (.shift w) C) = C ) := by
  classical
  intro w C
  cases C
  apply Prod.ext
  · rfl
  · simp only [BandPackingSymmetryCircleAction]
    ring

private theorem crAt426 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction (.shift
            w) (BandPackingSymmetryCircleAction (.shift (-w)) C) = C ) := by
  classical
  intro w C
  cases C
  apply Prod.ext
  · rfl
  · simp only [BandPackingSymmetryCircleAction]
    ring

private theorem zeroPhase :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (b : BandPackingSymmetry), ∀ (q : Fin 4 ->
            CircleCoordinates), BandPackingSymmetryQuadrupleAction (.comp a b) q =
            BandPackingSymmetryQuadrupleAction a (BandPackingSymmetryQuadrupleAction b q)) → (∀
            (g : BandPackingSymmetry), ∀ (k : BandPackingSymmetry), (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), BandPackingSymmetryQuadrupleAction k
            (BandPackingSymmetryQuadrupleAction g q) = q) → ((∀ (v : GaussianInt),
            BandPackingSymmetryVectorAction k (BandPackingSymmetryVectorAction g v) = v) → (∀ (q
            : Fin (4 : ℕ) → CircleCoordinates), (BandPackingSymmetryReversesOrientation (.comp k
            g) = false) → (BandPackingSymmetryScopedPhase (.comp k g) q false)))) ) := by
  classical
  intro composition g k ql vl q orientation
  simp [BandPackingSymmetryScopedPhase, composition, ql, orientation,
    BandPackingSymmetryVectorAction, vl]

end InversePhaseProof

theorem BandPackingSymmetryInversePhaseCancellation :
    (∀ (a : BandPackingSymmetry), ∀ (b : BandPackingSymmetry), ∀ (q : Fin 4 ->
        CircleCoordinates), ∀ (deltaB : Bool), ∀ (deltaA : Bool), ProperBandQuadruple q ->
      BandPackingSymmetryScopedPhase b q deltaB ->
      BandPackingSymmetryScopedPhase a
        (BandPackingSymmetryQuadrupleAction b q) deltaA ->
      BandPackingSymmetryScopedPhase (.comp a b) q (xor deltaB deltaA)) ∧
    ∀ g : BandPackingSymmetry, exists inverse : BandPackingSymmetry,
      (∀ C, BandPackingSymmetryCircleAction inverse
          (BandPackingSymmetryCircleAction g C) = C) ∧
      (∀ C, BandPackingSymmetryCircleAction g
          (BandPackingSymmetryCircleAction inverse C) = C) ∧
      (∀ q, BandPackingSymmetryQuadrupleAction inverse
          (BandPackingSymmetryQuadrupleAction g q) = q) ∧
      (∀ q, BandPackingSymmetryQuadrupleAction g
          (BandPackingSymmetryQuadrupleAction inverse q) = q) ∧
      (∀ T, BandPackingSymmetryTileAction inverse
          (BandPackingSymmetryTileAction g T) = T) ∧
      (∀ T, BandPackingSymmetryTileAction g
          (BandPackingSymmetryTileAction inverse T) = T) ∧
      (∀ v, BandPackingSymmetryVectorAction inverse
          (BandPackingSymmetryVectorAction g v) = v) ∧
      (∀ v, BandPackingSymmetryVectorAction g
          (BandPackingSymmetryVectorAction inverse v) = v) ∧
      (∀ h, BandPackingSymmetryPartialOdometerAction inverse
          (BandPackingSymmetryPartialOdometerAction g h) = h) ∧
      (∀ h, BandPackingSymmetryPartialOdometerAction g
          (BandPackingSymmetryPartialOdometerAction inverse h) = h) ∧
      ∀ (q : Fin 4 -> CircleCoordinates), (ProperBandQuadruple q) → (∀ (delta : Bool),
          BandPackingSymmetryScopedPhase g q delta ->
        BandPackingSymmetryScopedPhase inverse
          (BandPackingSymmetryQuadrupleAction g q) delta) := by
-- BODY
  classical
  have composition (a b : BandPackingSymmetry) (q : Fin 4 -> CircleCoordinates) :
      BandPackingSymmetryQuadrupleAction (.comp a b) q =
        BandPackingSymmetryQuadrupleAction a (BandPackingSymmetryQuadrupleAction b q) :=
            InversePhaseProof.composition a b q
  have phaseComposition := InversePhaseProof.phaseComposition composition
  have cancellations : forall g : BandPackingSymmetry, exists inverse : BandPackingSymmetry,
      BandPackingSymmetryReversesOrientation inverse = BandPackingSymmetryReversesOrientation g ∧
      (forall C, BandPackingSymmetryCircleAction inverse (BandPackingSymmetryCircleAction g C) =
          C) ∧
      (forall C, BandPackingSymmetryCircleAction g (BandPackingSymmetryCircleAction inverse C) =
          C) ∧
      (forall q, BandPackingSymmetryQuadrupleAction inverse (BandPackingSymmetryQuadrupleAction g
          q) = q) ∧
      (forall q, BandPackingSymmetryQuadrupleAction g (BandPackingSymmetryQuadrupleAction inverse
          q) = q) ∧
      (forall T, BandPackingSymmetryTileAction inverse (BandPackingSymmetryTileAction g T) = T) ∧
      (forall T, BandPackingSymmetryTileAction g (BandPackingSymmetryTileAction inverse T) = T) ∧
      (forall v, BandPackingSymmetryVectorAction inverse (BandPackingSymmetryVectorAction g v) =
          v) ∧
      (forall v, BandPackingSymmetryVectorAction g (BandPackingSymmetryVectorAction inverse v) =
          v) ∧
      (forall h, BandPackingSymmetryPartialOdometerAction inverse
          (BandPackingSymmetryPartialOdometerAction g h) = h) ∧
      (forall h, BandPackingSymmetryPartialOdometerAction g
          (BandPackingSymmetryPartialOdometerAction inverse h) = h) := by
    have qfour (v : GaussianInt) := InversePhaseProof.qfour v
    have invN (v : GaussianInt) : -GaussianQuarterTurn (GaussianQuarterTurn v) = v := by
      ext <;> simp [GaussianQuarterTurn]
    have invK (v : GaussianInt) : -GaussianReflection (-GaussianReflection v) = v := by
      ext <;> simp [GaussianReflection]
    have injN := InversePhaseProof.injN invN
    have injK := InversePhaseProof.injK invK
    have domain (g : BandPackingSymmetry) (h : PartialOdometer) := InversePhaseProof.domain g h
    have nvalue (h : PartialOdometer) (x : GaussianInt) := InversePhaseProof.nvalue invN injN h x
    have kvalue (h : PartialOdometer) (x : GaussianInt) := InversePhaseProof.kvalue invK injK h x
    have partial_ext (h k : PartialOdometer) (hd : h.domain = k.domain)
        (hv : ∀ x, h.value x = k.value x) := InversePhaseProof.partial_ext h k hd hv
    have tileN (T : ProtoTile) := InversePhaseProof.tileN qfour T
    have tileK (T : ProtoTile) := InversePhaseProof.tileK T
    have partialN (h : PartialOdometer) := InversePhaseProof.partialN qfour domain nvalue
        partial_ext h
    have partialK (h : PartialOdometer) := InversePhaseProof.partialK invK domain kvalue
        partial_ext h
    have potential (w x : GaussianInt) := InversePhaseProof.potential w x
    have partialShift (w : GaussianInt) (h : PartialOdometer) :
        BandPackingSymmetryPartialOdometerAction (.shift (-w))
          (BandPackingSymmetryPartialOdometerAction (.shift w) h) = h :=
              InversePhaseProof.partialShift partial_ext potential w h
    have quadCancel (g k : BandPackingSymmetry)
        (he : BandPackingSymmetryReversesOrientation k = BandPackingSymmetryReversesOrientation g)
        (hc : ∀ C, BandPackingSymmetryCircleAction k (BandPackingSymmetryCircleAction g C) = C)
        (q : Fin 4 -> CircleCoordinates) := InversePhaseProof.quadCancel g k he hc q
    intro g
    induction g with
    | identity =>
        refine ⟨.identity, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals intro x
        all_goals first | rfl | funext i; fin_cases i <;> rfl
    | negate =>
        let k : BandPackingSymmetry := .comp .negate (.comp .negate .negate)
        have he : BandPackingSymmetryReversesOrientation k =
            BandPackingSymmetryReversesOrientation .negate := rfl
        have cl (C : CircleCoordinates) := InversePhaseProof.clAt391 C
        have cr (C : CircleCoordinates) := InversePhaseProof.crAt395 C
        refine ⟨k, he, cl, cr, quadCancel _ _ he cl, quadCancel _ _ he.symm cr,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact tileN
        · exact tileN
        · exact qfour
        · exact qfour
        · exact partialN
        · exact partialN
    | conjugate =>
        have cl (C : CircleCoordinates) := InversePhaseProof.clAt408 C
        refine ⟨.conjugate, rfl, cl, cl, quadCancel _ _ rfl cl, quadCancel _ _ rfl cl,
          tileK, tileK, invK, invK, partialK, partialK⟩
    | shift w =>
        have cl (C : CircleCoordinates) := InversePhaseProof.clAt418 w C
        have cr (C : CircleCoordinates) := InversePhaseProof.crAt426 w C
        refine ⟨.shift (-w), rfl, cl, cr, quadCancel _ _ rfl cl, quadCancel _ _ rfl cr,
          fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, partialShift w, ?_⟩
        intro h
        simpa only [neg_neg] using partialShift (-w) h
    | comp a b ia ib =>
        rcases ia with ⟨ai, ae, acl, acr, aql, aqr, atl, atr, avl, avr, apl, apr⟩
        rcases ib with ⟨bi, be, bcl, bcr, bql, bqr, btl, btr, bvl, bvr, bpl, bpr⟩
        refine ⟨.comp bi ai, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [BandPackingSymmetryReversesOrientation, ae, be, Bool.xor_comm]
        · intro C
          simp only [BandPackingSymmetryCircleAction, acl, bcl]
        · intro C
          simp only [BandPackingSymmetryCircleAction, bcr, acr]
        · intro q
          rw [composition, composition, aql, bql]
        · intro q
          rw [composition, composition, bqr, aqr]
        · intro T
          simp only [BandPackingSymmetryTileAction, atl, btl]
        · intro T
          simp only [BandPackingSymmetryTileAction, btr, atr]
        · intro v
          simp only [BandPackingSymmetryVectorAction, avl, bvl]
        · intro v
          simp only [BandPackingSymmetryVectorAction, bvr, avr]
        · intro h
          simp only [BandPackingSymmetryPartialOdometerAction, apl, bpl]
        · intro h
          simp only [BandPackingSymmetryPartialOdometerAction, bpr, apr]
  refine ⟨phaseComposition, ?_⟩
  intro g
  rcases cancellations g with ⟨k, he, cl, cr, ql, qr, tl, tr, vl, vr, pl, pr⟩
  refine ⟨k, cl, cr, ql, qr, tl, tr, vl, vr, pl, pr, ?_⟩
  intro q hq delta hd
  have proper := BandPackingSymmetryProperCovariance g q hq
  obtain ⟨eta, hk, _⟩ := BandPackingSymmetryProjectiveVectorCovariance k _ proper
  have composed := phaseComposition k g q delta eta hq hd hk
  have orientation : BandPackingSymmetryReversesOrientation (.comp k g) = false := by
    simp [BandPackingSymmetryReversesOrientation, he]
  have zeroPhase := InversePhaseProof.zeroPhase composition g k ql vl q orientation
  have same := BandPackingSymmetryScopedPhaseUnique (.comp k g) q hq
    (xor delta eta) false composed zeroPhase
  have ed : eta = delta := by
    cases delta <;> cases eta <;> simp_all
  simpa only [ed] using hk

end ApollonianSuperharmonic

end
