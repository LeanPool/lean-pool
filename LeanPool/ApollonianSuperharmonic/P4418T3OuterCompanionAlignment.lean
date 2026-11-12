/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowTable
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.P3055T1SignedCentroidNormalForms
public import LeanPool.ApollonianSuperharmonic.P3045T1RightBoundaryDisplacementAlgebra
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing

-- [TABLET NODE: P4418T3OuterCompanionAlignment]

/-!
# P4418T3OuterCompanionAlignment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CompanionAlignmentGeometry

private theorem area_of_band :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (V : ProtoTile), 0 < c.1 → BandPrototile c V → TileArea V =
            Int.toNat c.1 ) := by
  classical
  intro c V hc hV
  cases hV with
  | line w x hw => simp at hc
  | unit z x anchor => simp [TileArea]
  | @decompose p hp S V hS hcells hfoot hcentroid =>
      exact (BandTileSimultaneousInduction p hp V
        (BandPrototile.decompose hp hS hcells hfoot hcentroid)).2.1

private theorem positive_parent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        ∀ (j : Fin 3), 0 < (q j.succ).1 ) := by
  classical
  intro C D T N h k x bundle q j
  let cfg := bundle.configuration
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 j
  have hne := cfg.noLine j.succ
  change 0 ≤ (q j.succ).1 at hn
  change (q j.succ).1 ≠ 0 at hne
  omega

private theorem occurrence_area :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (∀ (c : CircleCoordinates), ∀ (V : ProtoTile), 0 < c.1 → BandPrototile c V → TileArea V =
            Int.toNat c.1) → ((∀ (j : Fin 3), 0 < (q j.succ).1) → (∀ (a : PeriodicSubtileIndex),
            TileArea (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) = Int.toNat (q
            (slot a).succ).1)) ) := by
  classical
  intro C D T N h k x bundle placement q cert slot area_of_band positive_parent a
  have base_area (j : Fin 3) (b : Bool) (d : GaussianInt) :
      TileArea (TileTranslation (cert.P j b) d) =
        Int.toNat (q j.succ).1 := by
    rw [(TileDiskAreaCovariance _ _).2.2.2.1]
    exact area_of_band _ _ (positive_parent j) (cert.outer_occurrence j b).1
  cases a with
  | mk label m n =>
    cases label <;> simp [SubtileOccurrenceInterpretation, slot, base_area]

private theorem area_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (∀ (a : PeriodicSubtileIndex), TileArea (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v a) = Int.toNat (q (slot a).succ).1) → ((TileArea bundle.normalizedFixed =
            Int.toNat bundle.normalizedFixedCircle.1.1.1) → (Int.toNat
            bundle.normalizedFixedCircle.1.1.1 = Int.toNat (q (slot
            placement.exteriorIndex).succ).1)) ) := by
  classical
  intro C D T N h k x bundle placement q cert slot occurrence_area fixed_area
  rw [← fixed_area, ← occurrence_area placement.exteriorIndex]
  exact congrArg Finset.card placement.fixed_exterior_cells.symm

private theorem strict23 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (q 3).1 < (q 2).1 ) := by
  classical
  intro C D T N h k x bundle q
  let cfg := bundle.configuration
  have hp := cfg.secondProper.2 0
  change (cfg.secondPredecessor 1).1 < (cfg.secondPredecessor 0).1 at hp
  simpa only [cfg.secondChild, cfg.secondParentOne] using hp

private theorem parent_area_injective :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (fixedFunction : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h fixedFunction x),
            (BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedFixedCircle
            bundle.normalizedRoot bundle.normalizedFixed bundle.normalizedRootFunction
            bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces bundle.functions
            bundle.selectedSlot bundle.selectedSign bundle.routedDirection) → (
        let q := bundle.normalizedPresentation
        (∀ (j : Fin 3), 0 < (q j.succ).1) → (((q 3).1 < (q 2).1) → (∀ (j : Fin 3), ∀ (k : Fin 3),
            (Int.toNat (q j.succ).1 = Int.toNat (q k.succ).1) → (j = k)))) ) := by
  classical
  intro C D T N h fixedFunction x bundle placement q positive_parent strict23 j k heq
  let cfg := bundle.configuration
  have hj := positive_parent j
  have hk := positive_parent k
  have hc : (q j.succ).1 = (q k.succ).1 := by omega
  have h12 : (q 2).1 < (q 1).1 := cfg.order12
  fin_cases j <;> fin_cases k <;> simp_all
  all_goals omega

private theorem parent_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            ∀ (i : Fin (3 : ℕ)), (r i.succ = bundle.normalizedFixedCircle.1.1) → (
        let q := bundle.normalizedPresentation
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (Int.toNat bundle.normalizedFixedCircle.1.1.1 = Int.toNat (q (slot
            placement.exteriorIndex).succ).1) → ((∀ (j : Fin 3), ∀ (k : Fin 3), (Int.toNat (q
            j.succ).1 = Int.toNat (q k.succ).1) → (j = k)) → (∀ (rotation : Fin (3 : ℕ)), (∀ (j :
            Fin (3 : ℕ)), r j.succ = q (j + rotation).succ) → (bundle.normalizedFixedCircle.1.1 =
            q (slot placement.exteriorIndex).succ)))) ) := by
  classical
  intro C D T N h k x bundle placement r i hri q slot area_eq parent_area_injective rotation
      hrotation
  have heq := hrotation i
  have hj : i + rotation = slot placement.exteriorIndex := by
    apply parent_area_injective
    rw [← heq, hri]
    exact area_eq
  simpa only [hj, hri] using heq

private theorem presented_centroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), (r (0 : Fin (4 : ℕ)) =
            bundle.normalizedCircle.1.1) → ((r i.succ =
            bundle.normalizedFixedCircle.1.1) →
            ((TileCentroid bundle.normalizedFixed - TileCentroid bundle.normalizedRoot = (1 / 2 :
            ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) *
            (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ)))
            (r i.succ)))) → (
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (bundle.normalizedFixedCircle.1.1 = q (slot placement.exteriorIndex).succ) →
            ((TileCentroid bundle.normalizedFixed = TileCentroid (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v placement.exteriorIndex)) → (TileCentroid
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v placement.exteriorIndex) -
            TileCentroid bundle.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ s.val * (BandVectors.1 (q (slot placement.exteriorIndex).succ) (q 0) +
            BandVectors.1 (q 0) (q (slot placement.exteriorIndex).succ)))))))) ) := by
  classical
  intro C D T N h k x bundle placement r i s hr0 hri hcentroid q cert slot parent_eq fixed_centroid
  have root_eq : r 0 = q 0 := hr0.trans bundle.normalized_circle_eq.symm
  simpa only [fixed_centroid, root_eq, hri, parent_eq] using hcentroid

private theorem incoming :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (j : Fin 3), BandVectors.1 (q 0) (q j.succ) = (⟨0, 1⟩ : GaussianInt) * BandVectors.1
            (q j.succ) (q 0)) → (∀ (j : Fin 3), BandVectors.1 (q j.succ) (q 0) = -(⟨0, 1⟩ :
            GaussianInt) * BandVectors.1 (q 0) (q j.succ)) ) := by
  classical
  intro C D T N h k x bundle q flip j
  rw [flip]
  ext <;> simp

private theorem geometry :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        let turn : PeriodicSubtileIndex → Fin 4 := fun a =>
          match a.label with
          | .A => if a.first = -1 then 3 else 0
          | .B => if a.first = 1 then 1 else 2
          | .C => if a.second = 0 then 3 else 0
          | .D => if a.second = 0 then 1 else 2
          | .E => if a.first = 0 then 3 else 0
          | .F => if a.first = 0 then 1 else 2
        let shift : PeriodicSubtileIndex → GaussianInt := fun a =>
          match a.label with
          | .A => if a.first = -1 then -cert.u else cert.u
          | .B => if a.first = 1 then cert.u else -cert.u
          | .C => if a.second = 0 then -cert.v else cert.v
          | .D => if a.second = 0 then cert.v else -cert.v
          | .E => if a.first = 0 then cert.u + cert.v else -cert.u - cert.v
          | .F => if a.first = 0 then -cert.u - cert.v else cert.u + cert.v
        (BandVectors.1 (q 1) (q 0) = -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 1)) →
            ((BandVectors.1 (q 2) (q 0) = -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 2)) →
            ((BandVectors.1 (q 3) (q 0) = -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 3)) →
            ((cert.u = BandVectors.1 (q 0) (q 1)) → ((cert.v = BandVectors.1 (q 0) (q 2)) →
            ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = BandVectors.1 (q (2 :
            Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 :
            Fin (4 : ℕ))) = BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ)))) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = -BandVectors.1
            (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - BandVectors.1 (q (3 : Fin (4 : ℕ))) (q
            (2 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (3 : Fin
            (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((
        let I := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt);
        let U := BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)));
        let W := BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))); ∀ (j : Fin (3 : ℕ)),
            ∀ (s : Bool), TileCentroid (cert.P j s) = TileCentroid bundle.normalizedRoot + (if s
            = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • GaussianRealPoint (if j = (0 : Fin
            (3 : ℕ)) then ((1 : GaussianInt) - I) * W else if j = (1 : Fin (3 : ℕ)) then -((1 :
            GaussianInt) - I) * (U + W) else ((1 : GaussianInt) - I) * U)) → ((∀ (j : Fin 3), ∀
            (b : Bool), ∀ (d : GaussianInt), TileCentroid (TileTranslation (cert.P j b) d) =
            TileCentroid (cert.P j b) + GaussianRealPoint d) → (∀ (a : PeriodicSubtileIndex), (a
            = ⟨.A, -1, -1⟩ ∨ a = ⟨.A, 0, -1⟩ ∨
            a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
            a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨
            a = ⟨.B, 1, 1⟩ ∨ a = ⟨.B, 0, 1⟩ ∨
            a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
            a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩) → ((TileCentroid (SubtileOccurrenceInterpretation
                cert.P cert.u cert.v a) - TileCentroid bundle.normalizedRoot = (1 / 2 : ℝ) •
                GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (turn a).val * (BandVectors.1 (q
                (slot a).succ) (q 0) + BandVectors.1 (q 0) (q (slot a).succ)))) ∧ (⟨0, 1⟩ :
                GaussianInt) ^ (turn a).val * (if Even (turn a).val then BandVectors.1 (q 0) (q
                (slot a).succ) else BandVectors.1 (q (slot a).succ) (q 0)) = shift a))))))))))) )
                := by
  classical
  intro C D T N h k x bundle placement q cert slot turn shift hin1 hin2 hin3 period_u period_v
      hout1 hout2 hout3 signed_centroid translated_centroid a ha
  let cfg := bundle.configuration
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [slot, turn, shift]
    norm_num only
    try
    simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
    constructor
    · simp only [SubtileOccurrenceInterpretation, translated_centroid,
        signed_centroid]
      simp only [show (0 : Fin 3) ≠ 1 from by decide,
        show (1 : Fin 3) ≠ 0 from by decide,
        show (2 : Fin 3) ≠ 0 from by decide,
        show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false]
      simp only [hin1, hin2, hin3, period_u, period_v, hout1, hout2, hout3]
      ext <;>
        norm_num [GaussianRealPoint, pow_succ,
          -GaussianInt.intCast_re, -GaussianInt.intCast_im] <;> ring
    · simp only [Nat.even_iff]
      simp only [ite_true, ite_false,
        hin1, hin2, hin3, period_u, period_v, hout1, hout2, hout3]
      ext <;> norm_num [pow_succ] <;> ring

private theorem half_point_injective :
    (by
      classical
      exact
        ∀ (z : GaussianInt), ∀ (w : GaussianInt), ((1 / 2 : ℝ) • GaussianRealPoint z =
            (1 / 2 : ℝ) • GaussianRealPoint w) → (z = w) ) := by
  classical
  intro z w heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  simp only [GaussianRealPoint, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy
  apply Zsqrtd.ext
  · exact_mod_cast (show (z.re : ℝ) = (w.re : ℝ) by linarith)
  · exact_mod_cast (show (z.im : ℝ) = (w.im : ℝ) by linarith)

private theorem sum_ne :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (j : Fin 3), 0 < (q j.succ).1) → ((∀ (j : Fin 3), BandVectors.1 (q 0) (q j.succ) =
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q 0)) → (∀ (j : Fin 3),
            BandVectors.1 (q j.succ) (q 0) + BandVectors.1 (q 0) (q j.succ) ≠ 0)) ) := by
  classical
  intro C D T N h k x bundle q positive_parent flip j
  let cfg := bundle.configuration
  have hv := VectorNonvanishing q cfg.proper.1 j.succ 0
    (by exact Fin.succ_ne_zero j) (Or.inl (positive_parent j))
  rw [flip]
  convert mul_ne_zero (show (1 + (⟨0, 1⟩ : GaussianInt)) ≠ 0 by decide) hv
    using 1; ring

private theorem turn_injective :
    (by
      classical
      exact
        ∀ (a : Fin 4), ∀ (b : Fin 4), ((⟨0, 1⟩ : GaussianInt) ^ a.val =
            (⟨0, 1⟩ : GaussianInt) ^ b.val) → (a = b) ) := by
  classical
  intro a b heq
  fin_cases a <;> fin_cases b <;>
    norm_num [pow_succ, Zsqrtd.ext_iff] at heq <;> rfl

private theorem turn_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (s : Fin (4 : ℕ)),
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            placement.exteriorIndex) - TileCentroid bundle.normalizedRoot = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1 (q (slot
            placement.exteriorIndex).succ) (q 0) + BandVectors.1 (q 0) (q (slot
            placement.exteriorIndex).succ)))) → (
        let turn : PeriodicSubtileIndex → Fin 4 := fun a =>
          match a.label with
          | .A => if a.first = -1 then 3 else 0
          | .B => if a.first = 1 then 1 else 2
          | .C => if a.second = 0 then 3 else 0
          | .D => if a.second = 0 then 1 else 2
          | .E => if a.first = 0 then 3 else 0
          | .F => if a.first = 0 then 1 else 2
        (∀ (z : GaussianInt), ∀ (w : GaussianInt), ((1 / 2 : ℝ) • GaussianRealPoint z = (1 / 2 :
            ℝ) • GaussianRealPoint w) → (z = w)) → ((∀ (j : Fin 3), BandVectors.1 (q j.succ) (q
            0) + BandVectors.1 (q 0) (q j.succ) ≠ 0) → ((∀ (a : Fin 4), ∀ (b : Fin 4), ((⟨0, 1⟩ :
            GaussianInt) ^ a.val = (⟨0, 1⟩ : GaussianInt) ^ b.val) → (a = b)) → ((TileCentroid
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v placement.exteriorIndex) -
            TileCentroid bundle.normalizedRoot = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑(turn placement.exteriorIndex) : ℕ) * (BandVectors.1 (q (slot
            placement.exteriorIndex).succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q (slot placement.exteriorIndex).succ)))) → (s = turn
            placement.exteriorIndex))))) ) := by
  classical
  intro C D T N h k x bundle placement s q cert slot presented_centroid turn half_point_injective
      sum_ne turn_injective expected_centroid
  apply turn_injective
  apply mul_right_cancel₀ (sum_ne (slot placement.exteriorIndex))
  exact half_point_injective _ _ (presented_centroid.symm.trans expected_centroid)

private theorem shift_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralSubtilePlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixedCircle bundle.normalizedRoot
            bundle.normalizedFixed bundle.normalizedRootFunction bundle.normalizedFixedFunction
            bundle.normalizedPoint bundle.pieces bundle.functions bundle.selectedSlot
            bundle.selectedSign bundle.routedDirection), ∀ (r : Fin (4 : ℕ) → CircleCoordinates),
            ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), (r (0 : Fin (4 : ℕ)) =
            bundle.normalizedCircle.1.1) → ((r i.succ =
            bundle.normalizedFixedCircle.1.1) → (
        let q := bundle.normalizedPresentation
        let cert := placement.layout
        let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
          match a.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (bundle.normalizedFixedCircle.1.1 = q (slot placement.exteriorIndex).succ) → (
        let turn : PeriodicSubtileIndex → Fin 4 := fun a =>
          match a.label with
          | .A => if a.first = -1 then 3 else 0
          | .B => if a.first = 1 then 1 else 2
          | .C => if a.second = 0 then 3 else 0
          | .D => if a.second = 0 then 1 else 2
          | .E => if a.first = 0 then 3 else 0
          | .F => if a.first = 0 then 1 else 2
        let shift : PeriodicSubtileIndex → GaussianInt := fun a =>
          match a.label with
          | .A => if a.first = -1 then -cert.u else cert.u
          | .B => if a.first = 1 then cert.u else -cert.u
          | .C => if a.second = 0 then -cert.v else cert.v
          | .D => if a.second = 0 then cert.v else -cert.v
          | .E => if a.first = 0 then cert.u + cert.v else -cert.u - cert.v
          | .F => if a.first = 0 then -cert.u - cert.v else cert.u + cert.v
        (((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(turn placement.exteriorIndex) : ℕ) * if Even
            (↑(turn placement.exteriorIndex) : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            (slot placement.exteriorIndex).succ) else BandVectors.1 (q (slot
            placement.exteriorIndex).succ) (q (0 : Fin (4 : ℕ)))) = shift
            placement.exteriorIndex) → ((s = turn placement.exteriorIndex) → ((⟨0, 1⟩ :
            GaussianInt) ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r i.succ) else
            BandVectors.1 (r i.succ) (r 0)) = shift placement.exteriorIndex))))) ) := by
  classical
  intro C D T N h k x bundle placement r i s hr0 hri q cert slot parent_eq turn shift
      expected_shift turn_eq
  have root_eq : r 0 = q 0 := hr0.trans bundle.normalized_circle_eq.symm
  simpa only [turn_eq, root_eq, hri, parent_eq] using expected_shift

end CompanionAlignmentGeometry

theorem P4418T3OuterCompanionAlignment :
    ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
        PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
        BandOrderedGeneralSubtilePlacement
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixedCircle
      bundle.normalizedRoot bundle.normalizedFixed
      bundle.normalizedRootFunction bundle.normalizedFixedFunction
      bundle.normalizedPoint bundle.pieces bundle.functions
      bundle.selectedSlot bundle.selectedSign bundle.routedDirection), ∀ (row :
          BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedRoot placement.layout
      placement.exteriorIndex placement.centralIndex), ∀ (r : Fin 4 → CircleCoordinates), ∀ (i :
          Fin 3), ∀ (s : Fin 4), (ProperBandQuadruple r) → ((r 0 = bundle.normalizedCircle.1.1) →
          ((r i.succ = bundle.normalizedFixedCircle.1.1) → ((TileCentroid bundle.normalizedFixed -
        TileCentroid bundle.normalizedRoot =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
           BandVectors.1 (r 0) (r i.succ)))) → ((bundle.normalizedFixedSlope.1 -
        bundle.normalizedRootSlope.1 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).1) → ((bundle.normalizedFixedSlope.2 -
        bundle.normalizedRootSlope.2 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (r i.succ) (r 0) +
           BandVectors.2 (r 0) (r i.succ)))).2) → (bundle.normalizedFixedCircle.1.1 =
        bundle.normalizedPresentation
          (match placement.exteriorIndex.label with
            | .A | .B => 1 | .C | .D => 2 | .E | .F => 3) ∧
      s.val = (match placement.exteriorIndex.label with
        | .A => if placement.exteriorIndex.first = -1 then 3 else 0
        | .B => if placement.exteriorIndex.first = 1 then 1 else 2
        | .C => if placement.exteriorIndex.second = 0 then 3 else 0
        | .D => if placement.exteriorIndex.second = 0 then 1 else 2
        | .E => if placement.exteriorIndex.first = 0 then 3 else 0
        | .F => if placement.exteriorIndex.first = 0 then 1 else 2) ∧
      (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r 0) (r i.succ)
        else BandVectors.1 (r i.succ) (r 0)) =
      (match P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedRoot placement.layout row with
      | some z => z.oldShift
      | none => match placement.exteriorIndex.label with
        | .A => if placement.exteriorIndex.first = -1 then -placement.layout.u else
            placement.layout.u
        | .B => if placement.exteriorIndex.first = 1 then placement.layout.u else
            -placement.layout.u
        | .C => -placement.layout.v
        | .D => placement.layout.v
        | .E | .F => 0))))))) := by
  intro C D T N h k x bundle placement row r i s hr hr0 hri hcentroid hslopex hslopey
-- BODY
  classical
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let cert := placement.layout
  let slot : PeriodicSubtileIndex → Fin 3 := fun a =>
    match a.label with
    | .A | .B => 0
    | .C | .D => 1
    | .E | .F => 2
  -- Equal cell areas select a parent of the supplied presentation.
  have area_of_band : ∀ (c : CircleCoordinates) (V : ProtoTile),
      0 < c.1 → BandPrototile c V → TileArea V = Int.toNat c.1 :=
          CompanionAlignmentGeometry.area_of_band
  have positive_parent (j : Fin 3) : 0 < (q j.succ).1 :=
      CompanionAlignmentGeometry.positive_parent C D T N h k x bundle j
  have occurrence_area (a : PeriodicSubtileIndex) :
      TileArea (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) =
        Int.toNat (q (slot a).succ).1 := CompanionAlignmentGeometry.occurrence_area C D T N h k x
            bundle placement area_of_band positive_parent a
  have fixed_area : TileArea bundle.normalizedFixed =
      Int.toNat bundle.normalizedFixedCircle.1.1.1 :=
    area_of_band _ _ bundle.normalizedFixedCircle.2
      (TileOdometerBandPrototile _ _ _ bundle.normalized_fixed_odometer)
  have area_eq : Int.toNat bundle.normalizedFixedCircle.1.1.1 =
      Int.toNat (q (slot placement.exteriorIndex).succ).1 := CompanionAlignmentGeometry.area_eq C
          D T N h k x bundle placement occurrence_area fixed_area
  have strict23 : (q 3).1 < (q 2).1 := CompanionAlignmentGeometry.strict23 C D T N h k x bundle
  have parent_area_injective (j otherSlot : Fin 3)
      (heq : Int.toNat (q j.succ).1 = Int.toNat (q otherSlot.succ).1) : j = otherSlot :=
          CompanionAlignmentGeometry.parent_area_injective C D T N h k x bundle placement
          positive_parent strict23 j otherSlot heq
  obtain ⟨rotation, hrotation, _⟩ :=
    BandPredecessorNoCollision q r cfg.proper hr
      (bundle.normalized_circle_eq.trans hr0.symm)
  have parent_eq : bundle.normalizedFixedCircle.1.1 =
      q (slot placement.exteriorIndex).succ := CompanionAlignmentGeometry.parent_eq C D T N h k x
          bundle placement r i hri area_eq parent_area_injective rotation hrotation
  have fixed_centroid : TileCentroid bundle.normalizedFixed =
      TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        placement.exteriorIndex) :=
    (ProtoTileObservableExtensionality _ _ placement.fixed_exterior_cells
      placement.fixed_exterior_empty_anchor).2.2.2.2.symm
  have presented_centroid :
      TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        placement.exteriorIndex) - TileCentroid bundle.normalizedRoot =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q (slot placement.exteriorIndex).succ) (q 0) +
           BandVectors.1 (q 0) (q (slot placement.exteriorIndex).succ))) :=
               CompanionAlignmentGeometry.presented_centroid C D T N h k x bundle placement r i s
               hr0 hri hcentroid parent_eq fixed_centroid
  let turn : PeriodicSubtileIndex → Fin 4 := fun a =>
    match a.label with
    | .A => if a.first = -1 then 3 else 0
    | .B => if a.first = 1 then 1 else 2
    | .C => if a.second = 0 then 3 else 0
    | .D => if a.second = 0 then 1 else 2
    | .E => if a.first = 0 then 3 else 0
    | .F => if a.first = 0 then 1 else 2
  let shift : PeriodicSubtileIndex → GaussianInt := fun a =>
    match a.label with
    | .A => if a.first = -1 then -cert.u else cert.u
    | .B => if a.first = 1 then cert.u else -cert.u
    | .C => if a.second = 0 then -cert.v else cert.v
    | .D => if a.second = 0 then cert.v else -cert.v
    | .E => if a.first = 0 then cert.u + cert.v else -cert.u - cert.v
    | .F => if a.first = 0 then -cert.u - cert.v else cert.u + cert.v
  -- Calculate the twelve literal exterior positions in the common vector basis.
  have flip (j : Fin 3) : BandVectors.1 (q 0) (q j.succ) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q 0) :=
    ((VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper j).1
  have incoming (j : Fin 3) : BandVectors.1 (q j.succ) (q 0) =
      -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q j.succ) :=
          CompanionAlignmentGeometry.incoming C D T N h k x bundle flip j
  have hin1 : BandVectors.1 (q 1) (q 0) =
      -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 1) := incoming 0
  have hin2 : BandVectors.1 (q 2) (q 0) =
      -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 2) := incoming 1
  have hin3 : BandVectors.1 (q 3) (q 0) =
      -(⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 3) := incoming 2
  have period_u : cert.u = BandVectors.1 (q 0) (q 1) := cert.period_u
  have period_v : cert.v = BandVectors.1 (q 0) (q 2) := cert.period_v
  obtain ⟨_, _, _, _, hout1, hout2, hout3, _⟩ :=
    P3055T1ParentVectorNormalForms q cfg
  have signed_centroid := P3055T1SignedCentroidNormalForms q cfg
    bundle.normalizedCircle bundle.normalizedRoot cert
  have translated_centroid (j : Fin 3) (b : Bool) (d : GaussianInt) :
      TileCentroid (TileTranslation (cert.P j b) d) =
        TileCentroid (cert.P j b) + GaussianRealPoint d :=
    (TileTranslationFormulas _ _).2.2.2.2.1
  have geometry (a : PeriodicSubtileIndex)
      (ha : a = ⟨.A, -1, -1⟩ ∨ a = ⟨.A, 0, -1⟩ ∨
        a = ⟨.C, 1, 0⟩ ∨ a = ⟨.C, 1, 1⟩ ∨
        a = ⟨.E, 0, 1⟩ ∨ a = ⟨.E, -1, 0⟩ ∨
        a = ⟨.B, 1, 1⟩ ∨ a = ⟨.B, 0, 1⟩ ∨
        a = ⟨.D, -1, 0⟩ ∨ a = ⟨.D, -1, -1⟩ ∨
        a = ⟨.F, 0, -1⟩ ∨ a = ⟨.F, 1, 0⟩) :
      (TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) -
          TileCentroid bundle.normalizedRoot =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (turn a).val *
            (BandVectors.1 (q (slot a).succ) (q 0) +
             BandVectors.1 (q 0) (q (slot a).succ)))) ∧
      (⟨0, 1⟩ : GaussianInt) ^ (turn a).val *
        (if Even (turn a).val then BandVectors.1 (q 0) (q (slot a).succ)
          else BandVectors.1 (q (slot a).succ) (q 0)) = shift a :=
              CompanionAlignmentGeometry.geometry C D T N h k x bundle placement hin1 hin2 hin3
              period_u period_v hout1 hout2 hout3 signed_centroid translated_centroid a ha
  have half_point_injective (z w : GaussianInt)
      (heq : (1 / 2 : ℝ) • GaussianRealPoint z =
        (1 / 2 : ℝ) • GaussianRealPoint w) : z = w :=
            CompanionAlignmentGeometry.half_point_injective z w heq
  -- Nonvanishing makes the four centroid offsets distinct.
  have sum_ne (j : Fin 3) :
      BandVectors.1 (q j.succ) (q 0) + BandVectors.1 (q 0) (q j.succ) ≠ 0 :=
          CompanionAlignmentGeometry.sum_ne C D T N h k x bundle positive_parent flip j
  have turn_injective (a b : Fin 4)
      (heq : (⟨0, 1⟩ : GaussianInt) ^ a.val =
        (⟨0, 1⟩ : GaussianInt) ^ b.val) : a = b := CompanionAlignmentGeometry.turn_injective a b heq
  obtain ⟨expected_centroid, expected_shift⟩ :=
    geometry placement.exteriorIndex placement.exterior_index
  have turn_eq : s = turn placement.exteriorIndex := CompanionAlignmentGeometry.turn_eq C D T N h
      k x bundle placement s presented_centroid half_point_injective sum_ne turn_injective
      expected_centroid
  have shift_eq :
      (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (r 0) (r i.succ)
          else BandVectors.1 (r i.succ) (r 0)) = shift placement.exteriorIndex :=
              CompanionAlignmentGeometry.shift_eq C D T N h k x bundle placement r i s hr0 hri
              parent_eq expected_shift turn_eq
  refine ⟨?_, ?_, ?_⟩
  · cases hl : placement.exteriorIndex.label <;> simpa [slot, hl] using parent_eq
  · rw [turn_eq]
    cases hl : placement.exteriorIndex.label <;> simp [turn, hl]
    all_goals split_ifs <;> rfl
  · rw [shift_eq]
    generalize ha : placement.exteriorIndex = a at row ⊢
    generalize hb : placement.centralIndex = b at row
    cases row <;> simp [P3996T1SRowTable, shift, cert]

end ApollonianSuperharmonic

end
