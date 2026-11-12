/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerTrans
public import LeanPool.ApollonianSuperharmonic.AncestorOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.BoundaryStringConcatenation
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileStringExists
public import LeanPool.ApollonianSuperharmonic.TileStringUnique
public import LeanPool.ApollonianSuperharmonic.P4458T1FirstProperRows
public import LeanPool.ApollonianSuperharmonic.P4458T1LargestParentRows
public import LeanPool.ApollonianSuperharmonic.P4458T1SmallPairRows
public import LeanPool.ApollonianSuperharmonic.P4458T1SecondNewerRows
public import LeanPool.ApollonianSuperharmonic.P4458T1ThirdNewerRows
public import LeanPool.ApollonianSuperharmonic.P4458T1RespectAppend

-- [TABLET NODE: BoundaryStringOdometerRespect]

/-!
# BoundaryStringOdometerRespect

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryOdometerGeometry

private theorem dm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i :
            Fin (3 : ℕ)), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → (∀ (p₀ : ℝ ×
            ℝ), ∀ (pminus : ℝ × ℝ), (pminus - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ))) - BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ))) →
            (∀ (qb : Fin (4 : ℕ) → CircleCoordinates), (qb (0 : Fin (4 : ℕ)) = C₀.1.1) → ((qb
            i.succ = Cᵢ.1.1) → (pminus - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (qb
            i.succ) (qb 0) - BandVectors.2 (qb 0) (qb i.succ))))))) ) := by
  classical
  intro q C₀ Cᵢ i hC₀ hCᵢ p₀ pminus hdminus qb hb₀ hbᵢ
  simpa only [hb₀, hbᵢ, hC₀, hCᵢ] using hdminus

private theorem dp :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i :
            Fin (3 : ℕ)), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → (∀ (p₀ : ℝ ×
            ℝ), ∀ (pplus : ℝ × ℝ), (pplus - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ))) →
            (∀ (qb : Fin (4 : ℕ) → CircleCoordinates), (qb (0 : Fin (4 : ℕ)) = C₀.1.1) → ((qb
            i.succ = Cᵢ.1.1) → (pplus - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (qb
            i.succ) (qb 0) + BandVectors.2 (qb 0) (qb i.succ))))))) ) := by
  classical
  intro q C₀ Cᵢ i hC₀ hCᵢ p₀ pplus hdplus qb hb₀ hbᵢ
  simpa only [hb₀, hbᵢ, hC₀, hCᵢ] using hdplus

private theorem rv :
    (by
      classical
      exact
        ∀ (i : Fin (3 : ℕ)), ∀ (qb : Fin (4 : ℕ) → CircleCoordinates), (BandVectors.1 (qb (0 :
            Fin (4 : ℕ))) (qb i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (qb
            i.succ) (qb (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (qb (0 : Fin (4 : ℕ))) (qb i.succ) =
            -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (qb i.succ) (qb (0 : Fin (4 :
            ℕ)))) → ((⟨0, 1⟩ : GaussianInt) ^ 3 * (BandVectors.1 (qb i.succ) (qb 0) +
            BandVectors.1 (qb 0) (qb i.succ)) = BandVectors.1 (qb i.succ) (qb 0) - BandVectors.1
            (qb 0) (qb i.succ)) ) := by
  classical
  intro i qb flips
  rw [flips.1]
  ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem ra :
    (by
      classical
      exact
        ∀ (i : Fin (3 : ℕ)), ∀ (qb : Fin (4 : ℕ) → CircleCoordinates), (BandVectors.1 (qb (0 :
            Fin (4 : ℕ))) (qb i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (qb
            i.succ) (qb (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (qb (0 : Fin (4 : ℕ))) (qb i.succ) =
            -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (qb i.succ) (qb (0 : Fin (4 :
            ℕ)))) → ((-⟨0, 1⟩ : GaussianInt) ^ 3 * (BandVectors.2 (qb i.succ) (qb 0) +
            BandVectors.2 (qb 0) (qb i.succ)) = BandVectors.2 (qb i.succ) (qb 0) - BandVectors.2
            (qb 0) (qb i.succ)) ) := by
  classical
  intro i qb flips
  rw [flips.2]
  ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

private theorem adjacentMinus :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i : Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀
            (Rminus : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hminus : PartialOdometer),
            (TileOdometer C₀.1.1 T₀ h₀) → ((TileOdometer Cᵢ.1.1 Rminus hminus) → (∀ (p₀ : ℝ × ℝ),
            ∀ (pminus : ℝ × ℝ), (PartialOdometerSlope h₀ = some p₀) → ((PartialOdometerSlope
            hminus = some pminus) → (∀ (qb : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple qb) → ((qb (0 : Fin (4 : ℕ)) = C₀.1.1) → ((qb i.succ = Cᵢ.1.1) →
            ((TileCentroid Rminus - TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (qb i.succ) (qb (0 : Fin (4 : ℕ))) - BandVectors.1 (qb (0 : Fin (4 :
            ℕ))) (qb i.succ))) → ((pminus - p₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2
            (qb i.succ) (qb 0) - BandVectors.2 (qb 0) (qb i.succ))) → (((⟨0, 1⟩ : GaussianInt) ^
            3 * (BandVectors.1 (qb i.succ) (qb 0) + BandVectors.1 (qb 0) (qb i.succ)) =
            BandVectors.1 (qb i.succ) (qb 0) - BandVectors.1 (qb 0) (qb i.succ)) → (((-⟨0, 1⟩ :
            GaussianInt) ^ 3 * (BandVectors.2 (qb i.succ) (qb 0) + BandVectors.2 (qb 0) (qb
            i.succ)) = BandVectors.2 (qb i.succ) (qb 0) - BandVectors.2 (qb 0) (qb i.succ)) →
            (SubtileLatticeAdjacent C₀ Cᵢ T₀ Rminus h₀ hminus))))))))))) ) := by
  classical
  intro C₀ Cᵢ i T₀ Rminus h₀ hminus hO₀ hOminus p₀ pminus hs₀ hsminus qb hqb hb₀ hbᵢ hcminus dm
      rv ra
  refine ⟨hO₀, hOminus, p₀, pminus, hs₀, hsminus,
    qb, i, 3, hqb, hb₀, hbᵢ, ?_, ?_, ?_⟩
  · simpa only [show (3 : Fin 4).val = 3 from rfl, rv] using hcminus
  · simpa only [show (3 : Fin 4).val = 3 from rfl, ra, Prod.fst_sub] using congrArg Prod.fst dm
  · simpa only [show (3 : Fin 4).val = 3 from rfl, ra, Prod.snd_sub] using congrArg Prod.snd dm

private theorem adjacentPlus :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (i : Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀
            (Rplus : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hplus : PartialOdometer),
            (TileOdometer C₀.1.1 T₀ h₀) → ((TileOdometer Cᵢ.1.1 Rplus hplus) → (∀ (p₀ : ℝ × ℝ), ∀
            (pplus : ℝ × ℝ), (PartialOdometerSlope h₀ = some p₀) → ((PartialOdometerSlope hplus =
            some pplus) → (∀ (qb : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple qb) →
            ((qb (0 : Fin (4 : ℕ)) = C₀.1.1) → ((qb i.succ = Cᵢ.1.1) → ((TileCentroid Rplus -
            TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1 (qb i.succ) (qb (0 :
            Fin (4 : ℕ))) + BandVectors.1 (qb (0 : Fin (4 : ℕ))) (qb i.succ))) → ((pplus - p₀ =
            (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.2 (qb i.succ) (qb 0) + BandVectors.2 (qb
            0) (qb i.succ))) → (SubtileLatticeAdjacent C₀ Cᵢ T₀ Rplus h₀ hplus))))))))) ) := by
  classical
  intro C₀ Cᵢ i T₀ Rplus h₀ hplus hO₀ hOplus p₀ pplus hs₀ hsplus qb hqb hb₀ hbᵢ hcplus dp
  refine ⟨hO₀, hOplus, p₀, pplus, hs₀, hsplus,
    qb, i, 0, hqb, hb₀, hbᵢ, ?_, ?_, ?_⟩
  · simpa using hcplus
  · simpa using congrArg Prod.fst dp
  · simpa using congrArg Prod.snd dp

private theorem root :
    (by
      classical
      exact
        (ℕ) → (∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F :
            P4458T1BoundaryFrame C ε B R S g h), 1 < (F.q 0).1) ) := by
  classical
  intro n C ε B R S g h F
  have positive := C.property
  have smaller := F.proper.2 F.slot
  rw [F.parent] at smaller
  omega

private theorem ancestors :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F :
            P4458T1BoundaryFrame C ε B R S g h), ∀ (T : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (H :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (F.q i.succ) (T i s) (H i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            FootprintVertices (T i s) ⊆ FootprintVertices F.tile) → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), TileCentroid (T i s) - TileCentroid F.tile = (if s = true then (1 : ℝ) else
            (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (i + (2 : Fin (3 :
            ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1
            (F.q (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ))).2,
            (GaussianRealPoint (BandVectors.1 (F.q (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 :
            Fin (3 : ℕ))).succ))).1))) → ((∀ (x : GaussianInt), x ∈ F.odometer.domain ↔ ∃ (i :
            Fin (3 : ℕ)) (s : Bool), x ∈ (H i s).domain) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀
            x ∈ (H i s).domain, F.odometer.value x = (H i s).value x) → (∀ (j : Fin 3), ∀ (s :
            Bool), (0 < (F.q j.succ).1) → (AncestorOdometer (F.q j.succ) F.outer.1.1 (T j s)
            F.tile (H j s) F.odometer)))))) ) := by
  classical
  intro C ε B R S g h F T H hsub hfoot hcent hdom hvalue j s hj
  refine ⟨F.outer_odo, ?_,
    PositiveCurvatureTileOdometerDomain _ _ _ hj (hsub j s), ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      ⟨F.q, j, s, F.proper, F.child, rfl, F.outer_band,
        TileOdometerBandPrototile _ _ _ (hsub j s), hfoot j s, hcent j s⟩
  · intro x hx
    exact (hdom x).mpr ⟨j, s, hx⟩
  · intro x hx
    exact (hvalue j s x hx).symm

private theorem rotateProper :
    (by
      classical
      exact
        ∀ (u : Fin 4 → CircleCoordinates), (ProperBandQuadruple u) → (ProperBandQuadruple ![u 0,
            u 2, u 3, u 1]) ) := by
  classical
  intro u hu
  refine ⟨SemiProperQuadruple.rotate hu.1, ?_⟩
  intro j
  fin_cases j
  · simpa using hu.2 1
  · simpa using hu.2 2
  · simpa using hu.2 0

private theorem asymmetric :
    (by
      classical
      exact
        ∀ {X : CircleCoordinates}, ∀ {Y : CircleCoordinates}, (PrimitiveVectorOrientation X Y) →
            ((PrimitiveVectorOrientation Y X) → (False)) ) := by
  classical
  intro X Y hXY hYX
  have hex := ((PrimitiveVectorOrientationUnique X Y).2
    ((PrimitiveVectorOrientationUnique X Y).1 hXY)).2
  rcases hex with ⟨_, hn⟩ | ⟨_, hn⟩
  · exact hn hYX
  · exact hn hXY

private theorem unitPair :
    (by
      classical
      exact
        (ℕ) → (∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), (P4458T1BoundaryFrame
            C ε B R S g h) → (∀ (u : Fin 4 → CircleCoordinates), (ProperBandQuadruple u) → (((u
            2).1 = 1) → (((u 3).1 = 1) → ((PrimitiveVectorOrientation (u 2) (u 3) ∧
            UnitOccurrenceOrientation u 1 false ∧ UnitOccurrenceOrientation u 2 true) ∨
            (PrimitiveVectorOrientation (u 3) (u 2) ∧ UnitOccurrenceOrientation u 1 true ∧
            UnitOccurrenceOrientation u 2 false)))))) ) := by
  classical
  intro n C ε B R S g h F u hu hu2 hu3
  obtain ⟨_, _, _, _, inv, cases⟩ := BandOrientedBoundaryOccurrenceGenealogy u hu
  rcases cases with small | second | third
  · rcases small.2 with forward | backward
    · have cert := forward.2.2.2 hu2 hu3
      exact Or.inl ⟨forward.1, inv.1 hu2 false cert.1,
        inv.2 hu3 true cert.2.1⟩
    · have cert := backward.2.2.2 hu2 hu3
      exact Or.inr ⟨backward.1, inv.1 hu2 true cert.1,
        inv.2 hu3 false cert.2.1⟩
  · obtain ⟨t, ht, ht0, ht1, hlt, _⟩ := second
    omega
  · obtain ⟨t, ht, ht0, ht1, hlt, _⟩ := third
    omega

private theorem successorCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F :
            P4458T1BoundaryFrame C ε B R S g h), ∀ (T : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (H :
            Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (hsub : ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (F.q i.succ) (T i s) (H i s)), ∀ (hfoot : ∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), FootprintVertices (T i s) ⊆ FootprintVertices F.tile), ∀ (hcent : ∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), TileCentroid (T i s) - TileCentroid F.tile = (if s = true
            then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (i
            + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (i + (2 : Fin (3 : ℕ))).succ)
            (F.q (i + (1 : Fin (3 : ℕ))).succ))).1))), ∀ (hdom : ∀ (x : GaussianInt), x ∈
            F.odometer.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (H i s).domain), ∀ (hvalue :
            ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (H i s).domain, F.odometer.value x = (H i
            s).value x), ∀ (hslope : ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (F.q i.succ).1 = (0 : ℤ)
            ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope F.odometer = some p ∧
            PartialOdometerSlope (H i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (i + (2 : Fin (3 : ℕ))).succ)
            (F.q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (i + (2 : Fin (3
            : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (i + (2 : Fin
            (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q
            (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))), ∀
            (ancestors : ∀ (j : Fin 3), ∀ (s : Bool), (0 < (F.q j.succ).1) → (AncestorOdometer
            (F.q j.succ) F.outer.1.1 (T j s) F.tile (H j s) F.odometer)),
        let D : P4458T1RestrictionFamily F :=
          { tiles := T, functions := H, odometers := hsub
            occurrences := fun j s =>
              ⟨TileOdometerBandPrototile _ _ _ (hsub j s), hfoot j s, hcent j s⟩
            domain_subset := fun j s x hx => (hdom x).mpr ⟨j, s, hx⟩
            value_eq := fun j s x hx => (hvalue j s x hx).symm
            ancestors := ancestors, slopes := hslope }
        (∀ (u : Fin 4 → CircleCoordinates), (ProperBandQuadruple u) → (ProperBandQuadruple ![u 0,
            u 2, u 3, u 1])) → ((∀ {X : CircleCoordinates}, ∀ {Y : CircleCoordinates},
            (PrimitiveVectorOrientation X Y) → ((PrimitiveVectorOrientation Y X) → (False))) →
            ((∀ (u : Fin 4 → CircleCoordinates), (ProperBandQuadruple u) → (((u 2).1 = 1) → (((u
            3).1 = 1) → ((PrimitiveVectorOrientation (u 2) (u 3) ∧ UnitOccurrenceOrientation u 1
            false ∧ UnitOccurrenceOrientation u 2 true) ∨ (PrimitiveVectorOrientation (u 3) (u 2)
            ∧ UnitOccurrenceOrientation u 1 true ∧ UnitOccurrenceOrientation u 2 false))))) → (∀
            (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → ((![F.q 0,
            F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
            ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
                2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
              p 0, p 2, p 3]) → (Nonempty (P4458T1BoundaryPlacement F D)))))) ) := by
  classical
  intro C ε B R S g h F T H hsub hfoot hcent hdom hvalue hslope ancestors D rotateProper
      asymmetric unitPair a p hp hstep
  by_cases selected : F.slot = a
  · exact P4458T1LargestParentRows F D a p hp hstep selected
  have pq2 : p 2 = F.q (a + 1).succ := by
    simpa using (congrFun hstep 2).symm
  have pq3 : p 3 = F.q (a + 2).succ := by
    simpa using (congrFun hstep 3).symm
  obtain ⟨_, _, _, _, inv, cases⟩ := BandOrientedBoundaryOccurrenceGenealogy p hp
  have rotatedChart (hc : C.1.1.1 = 1) :
      UnitOccurrenceOrientation
        ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
        (F.slot - a) ε := by
    have hcq := F.chart hc
    fin_cases a
    · convert hcq using 1
      · funext j
        fin_cases j <;> congr 1
      · generalize F.slot = z
        fin_cases z <;> decide
    · have hcq' := UnitOccurrenceOrientation.rotate hcq
      convert hcq' using 1
      · funext j
        fin_cases j <;> rfl
      · generalize F.slot = z
        fin_cases z <;> decide
    · have hcq' := UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate hcq)
      convert hcq' using 1
      · funext j
        fin_cases j <;> rfl
      · generalize F.slot = z
        fin_cases z <;> decide
  have hB (hi : F.slot = a + 1) (hc : C.1.1.1 = 1) :
      UnitOccurrenceOrientation p 1 ε := by
    have hunit : (p 2).1 = 1 := by rw [pq2, ← hi, F.parent]; exact hc
    apply inv.1 hunit ε
    have hh := rotatedChart hc
    rw [hstep] at hh
    simpa [hi] using hh
  have hD (hi : F.slot = a + 2) (hc : C.1.1.1 = 1) :
      UnitOccurrenceOrientation p 2 ε := by
    have hunit : (p 3).1 = 1 := by rw [pq3, ← hi, F.parent]; exact hc
    apply inv.2 hunit ε
    have hh := rotatedChart hc
    rw [hstep] at hh
    simpa [hi] using hh
  rcases cases with small | second | third
  · exact P4458T1SmallPairRows F D a p hp hstep hB hD selected small.1
  · obtain ⟨t, ht, ht0, ht1, newer, transport⟩ := second
    have olderChart (hi : F.slot = a + 2) (hc : C.1.1.1 = 1) :
        UnitOccurrenceOrientation t 0 ε := by
      have data := transport ε (hD hi hc)
      by_cases hidden : (t 2).1 = 1
      · have htunit : (t 1).1 = 1 := by
          rw [ht1, pq3, ← hi, F.parent]
          exact hc
        let u : Fin 4 → CircleCoordinates := ![t 0, t 3, t 1, t 2]
        have hu : ProperBandQuadruple u := by
          simpa [u] using rotateProper _ (rotateProper t ht)
        have pairs := unitPair u hu (by simpa [u] using htunit)
          (by simpa [u] using hidden)
        have huChart : UnitOccurrenceOrientation u 1 ε := by
          rcases pairs with forward | backward
          · rcases data.2 hidden with ⟨arrow, label⟩ | ⟨arrow, label⟩
            · simpa only [label] using forward.2.1
            · exact (asymmetric (by simpa [u] using forward.1) arrow).elim
          · rcases data.2 hidden with ⟨arrow, label⟩ | ⟨arrow, label⟩
            · exact (asymmetric arrow (by simpa [u] using backward.1)).elim
            · simpa only [label] using backward.2.1
        have he : ![t 0, t 1, t 2, t 3] = t := by
          funext j
          fin_cases j <;> rfl
        simpa [u, he] using UnitOccurrenceOrientation.rotate huChart
      · exact data.1 hidden
    exact P4458T1SecondNewerRows F D a p hp hstep hB hD selected
      t ht ht0 ht1 newer olderChart
  · obtain ⟨t, ht, ht0, ht1, newer, transport⟩ := third
    have olderChart (hi : F.slot = a + 1) (hc : C.1.1.1 = 1) :
        UnitOccurrenceOrientation t 0 ε := by
      have data := transport ε (hB hi hc)
      by_cases hidden : (t 3).1 = 1
      · have htunit : (t 1).1 = 1 := by
          rw [ht1, pq2, ← hi, F.parent]
          exact hc
        let u : Fin 4 → CircleCoordinates := ![t 0, t 2, t 3, t 1]
        have hu : ProperBandQuadruple u := rotateProper t ht
        have pairs := unitPair u hu (by simpa [u] using hidden)
          (by simpa [u] using htunit)
        have huChart : UnitOccurrenceOrientation u 2 ε := by
          rcases pairs with forward | backward
          · rcases data.2 hidden with ⟨arrow, label⟩ | ⟨arrow, label⟩
            · exact (asymmetric (by simpa [u] using forward.1) arrow).elim
            · simpa only [label] using forward.2.2
          · rcases data.2 hidden with ⟨arrow, label⟩ | ⟨arrow, label⟩
            · simpa only [label] using backward.2.2
            · exact (asymmetric arrow (by simpa [u] using backward.1)).elim
        have he : ![t 0, t 1, t 2, t 3] = t := by
          funext j
          fin_cases j <;> rfl
        simpa [u, he] using
          UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate huChart)
      · exact data.1 hidden
    exact P4458T1ThirdNewerRows F D a p hp hstep hB hD selected
      t ht ht0 ht1 newer olderChart

private theorem placement :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F :
            P4458T1BoundaryFrame C ε B R S g h), ∀ (T : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (H :
            Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (hsub : ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            TileOdometer (F.q i.succ) (T i s) (H i s)), ∀ (hfoot : ∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), FootprintVertices (T i s) ⊆ FootprintVertices F.tile), ∀ (hcent : ∀ (i : Fin
            (3 : ℕ)), ∀ (s : Bool), TileCentroid (T i s) - TileCentroid F.tile = (if s = true
            then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (i
            + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (i + (2 : Fin (3 : ℕ))).succ)
            (F.q (i + (1 : Fin (3 : ℕ))).succ))).1))), ∀ (hdom : ∀ (x : GaussianInt), x ∈
            F.odometer.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (H i s).domain), ∀ (hvalue :
            ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (H i s).domain, F.odometer.value x = (H i
            s).value x), ∀ (hslope : ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (F.q i.succ).1 = (0 : ℤ)
            ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope F.odometer = some p ∧
            PartialOdometerSlope (H i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (i + (2 : Fin (3 : ℕ))).succ)
            (F.q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (i + (2 : Fin (3
            : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (i + (2 : Fin
            (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q
            (i + (2 : Fin (3 : ℕ))).succ) (F.q (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ))), ∀
            (ancestors : ∀ (j : Fin 3), ∀ (s : Bool), (0 < (F.q j.succ).1) → (AncestorOdometer
            (F.q j.succ) F.outer.1.1 (T j s) F.tile (H j s) F.odometer)),
        let D : P4458T1RestrictionFamily F :=
          { tiles := T, functions := H, odometers := hsub
            occurrences := fun j s =>
              ⟨TileOdometerBandPrototile _ _ _ (hsub j s), hfoot j s, hcent j s⟩
            domain_subset := fun j s x hx => (hdom x).mpr ⟨j, s, hx⟩
            value_eq := fun j s x hx => (hvalue j s x hx).symm
            ancestors := ancestors, slopes := hslope }
        (∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → ((![F.q 0,
            F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 *
            (p 3).1 - (p 1).1, 2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p
            3]) → (Nonempty (P4458T1BoundaryPlacement F D)))) → (Nonempty
            (P4458T1BoundaryPlacement F D)) ) := by
  classical
  intro C ε B R S g h F T H hsub hfoot hcent hdom hvalue hslope ancestors D successorCase
  rcases BandParentBoundaryGenealogy F.q F.proper with roots | first | second | third
  · exact P4458T1FirstProperRows F D roots
  · obtain ⟨p, hp, hs, _⟩ := first
    apply successorCase 0 p hp
    convert hs using 1
    funext j
    fin_cases j <;> rfl
  · obtain ⟨p, hp, hs, _⟩ := second
    exact successorCase 1 p hp (by simpa using hs)
  · obtain ⟨p, hp, hs, _⟩ := third
    exact successorCase 2 p hp (by simpa using hs)

private theorem realize :
    (by
      classical
      exact
        ∀ (n : ℕ), (∀ m < n, ∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R :
            ProtoTile), ∀ (S : ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F
            : P4458T1BoundaryFrame C ε B R S g h), F.outer.1.1.1.toNat = m → ∃ (ts : List
                ProtoTile) (fs : List PartialOdometer),
            fs.head? = some g ∧ fs.getLast? = some h ∧ OdometerStringRespect C ε B R S ts fs ∧ ∀
            U ∈ (List.drop (1 : ℕ) ts).dropLast, ∃ (k : PartialOdometer), (U, k) ∈ ts.zip fs ∧
            AncestorOdometer C.1.1 F.outer.1.1 U F.tile
            k F.odometer) → (∀ (C : BandCircle), ∀ (ε : Bool), ∀ (B : ProtoTile), ∀ (R :
            ProtoTile), ∀ (S : ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer), ∀ (F
            : P4458T1BoundaryFrame C ε B R S g h), (F.outer.1.1.1.toNat = n) → (∀
                {U : ProtoTile}, ∀ {V : ProtoTile}, ∀
            {k : PartialOdometer}, ∀ {l : PartialOdometer}, (P4458T1BoundarySide F U V k l) →
            (∃ ts fs, fs.head? = some k ∧ fs.getLast? = some l ∧ OdometerStringRespect C ε B U V
            ts fs ∧ ∀ W ∈ (ts.drop 1).dropLast, ∃ m, (W, m) ∈ ts.zip fs ∧ AncestorOdometer C.1.1
            F.outer.1.1 W F.tile m F.odometer))) ) := by
  classical
  intro n ih C ε B R S g h F hn U V k l side
  cases side with
  | direct string link =>
    refine ⟨[U, V], [k, l], by simp, by simp, ?_, ?_⟩
    · refine ⟨string, List.Forall₂.cons link.1
        (List.Forall₂.cons link.2.1 List.Forall₂.nil), ?_⟩
      simpa [List.IsChain, List.isChain_pair] using link
    · simp
  | recursive G j parent ancestor =>
    have smaller : G.outer.1.1.1 < F.outer.1.1.1 := by
      simpa only [← parent, F.child] using F.proper.2 j
    have decrease : G.outer.1.1.1.toNat < n := by
      have positive := G.outer.property
      omega
    obtain ⟨ts, hts⟩ := TileStringExists C ε B U V
      G.base_band G.minus_family G.plus_family
    obtain ⟨us, fs, head, last, respect, inner⟩ :=
      ih G.outer.1.1.1.toNat decrease C ε B U V k l G rfl
    have same := TileStringUnique C ε B U V us ts respect.1 hts
    subst us
    refine ⟨ts, fs, head, last, respect, ?_⟩
    intro W hW
    obtain ⟨m, hm, ha⟩ := inner W hW
    exact ⟨m, hm, AncestorOdometerTrans _ _ _ _ _ _ _ _ _ ha ancestor⟩

end BoundaryOdometerGeometry

theorem BoundaryStringOdometerRespect :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (C₀ : BandCircle), ∀ (Cᵢ :
        BandCircle), ∀ (i : Fin 3), (q 0 = C₀.1.1) → ((q i.succ = Cᵢ.1.1) → (∀ (orientation :
        Bool), ∀ (T₀ : ProtoTile), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀ (Rplus :
        ProtoTile), ∀ (tiles : List ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hminus :
        PartialOdometer), ∀ (hplus : PartialOdometer), (TileOdometer C₀.1.1 T₀ h₀) →
        ((BoundaryString C₀ Cᵢ i orientation T₀ base Rminus Rplus tiles) → ((TileOdometer Cᵢ.1.1
        Rminus hminus) → ((TileOdometer Cᵢ.1.1 Rplus hplus) → (∀ (p₀ : ℝ × ℝ), ∀ (pminus : ℝ ×
        ℝ), ∀ (pplus : ℝ × ℝ), (PartialOdometerSlope h₀ = some p₀) → ((PartialOdometerSlope
        hminus = some pminus) → ((PartialOdometerSlope hplus = some pplus) → ((pminus - p₀ = (1 /
        2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (q i.succ) (q 0) - BandVectors.2 (q 0) (q i.succ))) → ((pplus - p₀ = (1 / 2
          : ℝ) • GaussianRealPoint
      (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) →
          (SubtileLatticeAdjacent C₀ Cᵢ T₀ Rminus h₀ hminus ∧
    SubtileLatticeAdjacent C₀ Cᵢ T₀ Rplus h₀ hplus ∧
    (∀ T ∈ (tiles.drop 1).dropLast, FootprintVertices T ⊆ FootprintVertices T₀) ∧
    ∃ hs : List PartialOdometer,
      hs.head? = some hminus ∧ hs.getLast? = some hplus ∧
      OdometerStringRespect Cᵢ orientation base Rminus Rplus tiles hs ∧
      ∀ T ∈ (tiles.drop 1).dropLast,
        ∃ h, (T, h) ∈ tiles.zip hs ∧
          AncestorOdometer Cᵢ.1.1 C₀.1.1 T T₀ h h₀)))))))))))) := by
  intro q hq C₀ Cᵢ i hC₀ hCᵢ orientation T₀ base Rminus Rplus tiles h₀ hminus hplus hO₀ hstring
      hOminus hOplus p₀ pminus pplus hs₀ hsminus hsplus hdminus hdplus
-- BODY
  classical
  obtain ⟨qb, hqb, hb₀, hbᵢ, hT₀, hchart, htiles, hcminus, hcplus⟩ := hstring
  have dm := BoundaryOdometerGeometry.dm q C₀ Cᵢ i hC₀ hCᵢ p₀ pminus hdminus qb hb₀ hbᵢ
  have dp := BoundaryOdometerGeometry.dp q C₀ Cᵢ i hC₀ hCᵢ p₀ pplus hdplus qb hb₀ hbᵢ
  have flips := (VectorRecursionLaws qb hqb.1).2.2.2.2 hqb i
  have adjacentMinus := BoundaryOdometerGeometry.adjacentMinus C₀ Cᵢ i T₀ Rminus h₀ hminus hO₀
      hOminus p₀ pminus hs₀ hsminus qb hqb hb₀ hbᵢ hcminus dm (BoundaryOdometerGeometry.rv i qb
      flips) (BoundaryOdometerGeometry.ra i qb flips)
  have adjacentPlus := BoundaryOdometerGeometry.adjacentPlus C₀ Cᵢ i T₀ Rplus h₀ hplus hO₀ hOplus
      p₀ pplus hs₀ hsplus qb hqb hb₀ hbᵢ hcplus dp
  let initial : P4458T1BoundaryFrame Cᵢ orientation base Rminus Rplus hminus hplus :=
    { outer := C₀, q := qb, proper := hqb, slot := i, child := hb₀, parent := hbᵢ
      tile := T₀, odometer := h₀, outer_odo := hO₀, minus_odo := hOminus
      plus_odo := hOplus, outer_band := hT₀, base_band := htiles.1
      minus_family := htiles.2.2.2.2.1 _ (List.mem_of_mem_head? htiles.2.1)
      plus_family := htiles.2.2.2.2.1 _ (List.mem_of_getLast? htiles.2.2.1)
      chart := hchart, minus_centroid := hcminus, plus_centroid := hcplus
      outerSlope := p₀, minusSlope := pminus, plusSlope := pplus
      slope_outer := hs₀, slope_minus := hsminus, slope_plus := hsplus
      minus_difference := dm, plus_difference := dp }
  have construct : ∀ n : ℕ, ∀ (C : BandCircle) (ε : Bool)
      (B R S : ProtoTile) (g h : PartialOdometer)
      (F : P4458T1BoundaryFrame C ε B R S g h),
      F.outer.1.1.1.toNat = n →
      ∃ ts fs, fs.head? = some g ∧ fs.getLast? = some h ∧
        OdometerStringRespect C ε B R S ts fs ∧
        ∀ U ∈ (ts.drop 1).dropLast,
          ∃ k, (U, k) ∈ ts.zip fs ∧
            AncestorOdometer C.1.1 F.outer.1.1 U F.tile k F.odometer := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C ε B R S g h F hn
      have root := BoundaryOdometerGeometry.root n C ε B R S g h F
      obtain ⟨T, H, hband, hsub, hcells, hfoot, hcent, hdom, hvalue, hcompat, hslope⟩ :=
        TileOdometerReindexedDecomposition F.q F.proper F.tile F.odometer root
          (by simpa only [F.child] using F.outer_odo)
      have ancestors := BoundaryOdometerGeometry.ancestors C ε B R S g h F T H hsub hfoot hcent
          hdom hvalue
      let D : P4458T1RestrictionFamily F :=
        { tiles := T, functions := H, odometers := hsub
          occurrences := fun j s =>
            ⟨TileOdometerBandPrototile _ _ _ (hsub j s), hfoot j s, hcent j s⟩
          domain_subset := fun j s x hx => (hdom x).mpr ⟨j, s, hx⟩
          value_eq := fun j s x hx => (hvalue j s x hx).symm
          ancestors := ancestors, slopes := hslope }
      -- A hidden unit is resolved through a second literal successor.
      have placement := BoundaryOdometerGeometry.placement C ε B R S g h F T H hsub hfoot hcent
          hdom hvalue hslope ancestors (BoundaryOdometerGeometry.successorCase C ε B R S g h F T
          H hsub hfoot hcent hdom hvalue hslope ancestors (BoundaryOdometerGeometry.rotateProper)
          (BoundaryOdometerGeometry.asymmetric) (BoundaryOdometerGeometry.unitPair n C ε B R S g
          h F))
      obtain ⟨P⟩ := placement
      have realize {U V : ProtoTile} {k l : PartialOdometer}
          (side : P4458T1BoundarySide F U V k l) := BoundaryOdometerGeometry.realize n ih C ε B
              R S g h F hn (U := U) (V := V) (k := k) (l := l) side
      obtain ⟨left, hl, hlhead, hllast, hleft, hleftAnc⟩ := realize P.left
      obtain ⟨right, hr, hrhead, hrlast, hright, hrightAnc⟩ := realize P.right
      have chart (hc : (F.q F.slot.succ).1 = 1) :
          UnitOccurrenceOrientation F.q F.slot ε := F.chart (by simpa [F.parent] using hc)
      obtain ⟨_, _, joined⟩ :=
        BoundaryStringConcatenation F.q F.proper F.outer C F.slot F.child F.parent
          ε ε ε chart chart chart F.tile B P.join R S left right
          (by simpa only [F.child] using F.outer_band)
          (by simpa using P.occurrence.2.2)
          F.minus_centroid F.plus_centroid hleft.1 hright.1
      obtain ⟨_, _, _, _, _, _, hjoined, _, _⟩ := joined
      have appended := P4458T1RespectAppend C F.outer ε B R P.join S F.tile
        g (D.functions F.slot false) h F.odometer left right hl hr
        hleft hright hlhead hllast hrhead hrlast hjoined P.ancestor hleftAnc hrightAnc
      exact ⟨left.dropLast ++ right, hl.dropLast ++ hr, appended⟩
  obtain ⟨ts, fs, head, last, respect, inner⟩ :=
    construct C₀.1.1.1.toNat Cᵢ orientation base Rminus Rplus hminus hplus initial rfl
  have same := TileStringUnique Cᵢ orientation base Rminus Rplus ts tiles respect.1 htiles
  subst ts
  refine ⟨adjacentMinus, adjacentPlus, ?_, fs, head, last, respect, inner⟩
  intro U hU
  obtain ⟨k, _, ha⟩ := inner U hU
  have domain := PositiveCurvatureTileOdometerDomain C₀.1.1 T₀ h₀ C₀.property hO₀
  intro x hx
  rw [← domain]
  exact ha.2.2.2.1 ((show
      x ∈ k.domain
    from by
      classical
      change x ∈ (k.domain : Set GaussianInt)
      rw [ha.2.2.1]
      exact hx))

end ApollonianSuperharmonic

end
