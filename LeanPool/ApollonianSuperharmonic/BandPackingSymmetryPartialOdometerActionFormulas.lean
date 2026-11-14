/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.P2999T1OrthogonalSlopeTransport
public import LeanPool.ApollonianSuperharmonic.P2999T1ShiftSlopeTransport

-- [TABLET NODE: BandPackingSymmetryPartialOdometerActionFormulas]

/-!
# BandPackingSymmetryPartialOdometerActionFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPackingSymmetryPartialOdometerActionFormulas
    (g : BandPackingSymmetry) (h k : PartialOdometer) :
    (((BandPackingSymmetryPartialOdometerAction g h).domain :
        Set GaussianInt) =
      BandPackingSymmetryVectorAction g '' (h.domain : Set GaussianInt)) ∧
    BandPackingSymmetryPartialOdometerAction .identity h = h ∧
    (∀ w x, x ∈ h.domain →
      (BandPackingSymmetryPartialOdometerAction (.shift w) h).value x =
        h.value x + BandPackingShiftPotential w x) ∧
    (∀ x, x ∈ (BandPackingSymmetryPartialOdometerAction .negate h).domain →
      (BandPackingSymmetryPartialOdometerAction .negate h).value x =
        h.value (-GaussianQuarterTurn x)) ∧
    (∀ x, x ∈
        (BandPackingSymmetryPartialOdometerAction .conjugate h).domain →
      (BandPackingSymmetryPartialOdometerAction .conjugate h).value x =
        h.value (-GaussianReflection x)) ∧
    (∀ a b,
      BandPackingSymmetryPartialOdometerAction (.comp a b) h =
        BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b h)) ∧
    (OdometerCompatibility
        (BandPackingSymmetryPartialOdometerAction g h)
        (BandPackingSymmetryPartialOdometerAction g k) ↔
      OdometerCompatibility h k) ∧
    ∀ T : ProtoTile, T.cells.Nonempty →
      PartialOdometerSquares h = T.cells →
      PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) =
        (PartialOdometerSlope h).map
          (BandPackingSymmetrySlopeAction g T) := by
-- BODY
  classical
  have invN (x : GaussianInt) : -GaussianQuarterTurn (GaussianQuarterTurn x) = x := by
    ext <;> simp [GaussianQuarterTurn]
  have invK (x : GaussianInt) : -GaussianReflection (-GaussianReflection x) = x := by
    ext <;> simp [GaussianReflection]
  have injN : Function.Injective GaussianQuarterTurn := by
    intro x y he
    simpa only [invN] using congrArg (fun z => -GaussianQuarterTurn z) he
  have injK : Function.Injective (fun x => -GaussianReflection x) := by
    intro x y he
    simpa only [invK] using congrArg (fun z => -GaussianReflection z) he
  have injective (g : BandPackingSymmetry) :
      Function.Injective (BandPackingSymmetryVectorAction g) := by
    induction g with
    | identity => exact Function.injective_id
    | shift w => exact Function.injective_id
    | negate => exact injN
    | conjugate => exact injK
    | comp a b ia ib => exact ia.comp ib
  have domain (g : BandPackingSymmetry) (h : PartialOdometer) :
      ((BandPackingSymmetryPartialOdometerAction g h).domain : Set GaussianInt) =
        BandPackingSymmetryVectorAction g '' (h.domain : Set GaussianInt) := by
    induction g generalizing h with
    | identity => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
    | shift w => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
    | negate => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
    | conjugate => simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
    | comp a b ia ib =>
      simp only [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetryVectorAction]
      rw [ia, ib, Set.image_image]
  have forward (g : BandPackingSymmetry) (h : PartialOdometer) (x : GaussianInt)
      (hx : x ∈ h.domain) :
      BandPackingSymmetryVectorAction g x ∈
        (BandPackingSymmetryPartialOdometerAction g h).domain := by
    change BandPackingSymmetryVectorAction g x ∈
      ((BandPackingSymmetryPartialOdometerAction g h).domain : Set GaussianInt)
    rw [domain]
    exact ⟨x, hx, rfl⟩
  have difference (g : BandPackingSymmetry) (h k : PartialOdometer)
      (x : GaussianInt) (hx : x ∈ h.domain) (hk : x ∈ k.domain) :
      (BandPackingSymmetryPartialOdometerAction g k).value
          (BandPackingSymmetryVectorAction g x) -
        (BandPackingSymmetryPartialOdometerAction g h).value
          (BandPackingSymmetryVectorAction g x) = k.value x - h.value x := by
    induction g generalizing h k x with
    | identity => rfl
    | shift w =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        hx, hk, ↓reduceIte]
      ring
    | negate =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem GaussianQuarterTurn hx,
        Finset.mem_image_of_mem GaussianQuarterTurn hk, ↓reduceIte, invN]
    | conjugate =>
      simp only [BandPackingSymmetryVectorAction, BandPackingSymmetryPartialOdometerAction,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) hx,
        Finset.mem_image_of_mem (fun z => -GaussianReflection z) hk, ↓reduceIte, invK]
    | comp a b ia ib =>
      exact (ia _ _ _ (forward b h x hx) (forward b k x hk)).trans (ib h k x hx hk)
  have compatible (h k : PartialOdometer) :
      OdometerCompatibility h k ↔
        ∃ c : ℤ, ∀ x, x ∈ h.domain → x ∈ k.domain → k.value x - h.value x = c := by
    constructor
    · rintro (hd | hc)
      · refine ⟨0, fun x hx hk => ?_⟩
        exact (Set.disjoint_left.mp hd hx hk).elim
      · exact hc
    · exact Or.inr
  have compatibility :
      OdometerCompatibility (BandPackingSymmetryPartialOdometerAction g h)
        (BandPackingSymmetryPartialOdometerAction g k) ↔ OdometerCompatibility h k := by
    rw [compatible, compatible]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, fun x hx hk => ?_⟩
      rw [← difference g h k x hx hk]
      exact hc _ (forward g h x hx) (forward g k x hk)
    · rintro ⟨c, hc⟩
      refine ⟨c, fun y hyh hyk => ?_⟩
      change y ∈ ((BandPackingSymmetryPartialOdometerAction g h).domain : Set GaussianInt) at hyh
      change y ∈ ((BandPackingSymmetryPartialOdometerAction g k).domain : Set GaussianInt) at hyk
      rw [domain] at hyh hyk
      obtain ⟨x, hx, rfl⟩ := hyh
      obtain ⟨z, hz, he⟩ := hyk
      have zx : z = x := (injective g) he
      subst z
      rw [difference g h k x hx hz]
      exact hc x hx hz
  refine ⟨domain g h, rfl, ?_, ?_, ?_, ?_, compatibility, ?_⟩
  · intro w x hx
    simp [BandPackingSymmetryPartialOdometerAction, hx]
  · intro x hx
    change x ∈ h.domain.image GaussianQuarterTurn at hx
    simp only [BandPackingSymmetryPartialOdometerAction, ite_eq_left hx]
  · intro x hx
    change x ∈ h.domain.image (fun z => -GaussianReflection z) at hx
    simp only [BandPackingSymmetryPartialOdometerAction, ite_eq_left hx]
  · intro a b
    rfl
  · clear compatibility
    have nonempty (g : BandPackingSymmetry) (T : ProtoTile) (hne : T.cells.Nonempty) :
        (BandPackingSymmetryTileAction g T).cells.Nonempty := by
      induction g generalizing T with
      | identity => exact hne
      | shift w => exact hne
      | negate => exact hne.image _
      | conjugate => exact ((hne.image _).image _).image _
      | comp a b ia ib => exact ia _ (ib T hne)
    induction g generalizing h with
    | identity =>
      intro T hne hT
      simp [BandPackingSymmetryPartialOdometerAction, BandPackingSymmetrySlopeAction]
    | shift w => exact fun T hne hT => P2999T1ShiftSlopeTransport h w T hne hT
    | negate =>
      intro T hne hT
      exact (P2999T1OrthogonalSlopeTransport h).1
    | conjugate =>
      intro T hne hT
      exact (P2999T1OrthogonalSlopeTransport h).2
    | comp a b ia ib =>
      intro T hne hT
      change PartialOdometerSlope
        (BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b h)) = _
      rw [ia _ (BandPackingSymmetryTileAction b T) (nonempty b T hne)
        (P2999T1CompleteSquareTransport b h T hT), ib h T hne hT]
      simp only [Option.map_map, BandPackingSymmetrySlopeAction, Function.comp_def]

end ApollonianSuperharmonic

end
