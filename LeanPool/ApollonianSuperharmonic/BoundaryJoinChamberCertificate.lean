/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TriangularSignedHeight
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.P4994T6RotationLaws
public import LeanPool.ApollonianSuperharmonic.P4994T6NonunitChamber
public import LeanPool.ApollonianSuperharmonic.P4994T6UnitOccurrenceChamber
public import LeanPool.ApollonianSuperharmonic.P4994T6UnitChartRotation

-- [TABLET NODE: BoundaryJoinChamberCertificate]

/-!
# BoundaryJoinChamberCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BoundaryJoinChamberCertificate
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (C : BandCircle) (i : Fin 3) (hC : q i.succ = C.1.1)
    (orientation : Bool)
    (horientation : (q i.succ).1 = 1 →
      UnitOccurrenceOrientation q i orientation)
    (base : ProtoTile) (hbase : BandPrototile C.1.1 base)
    (e f : GaussianInt)
    (hdet : 0 < e.re * f.im - e.im * f.re)
    (he : e ∈ TilingLattice C) (hf : f ∈ TilingLattice C)
    (hcoord : ∀ w : TilingLattice C, ∃! z : Int × Int,
      (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f =
        (w : GaussianInt))
    (hadj : ∀ x y : Int × Int,
      (if C.1.1.1 = 1 then
        ∃ t : GaussianInt,
          UnitTriangularStep orientation t ∧
          TileCentroid (TileTranslation base
              ((y.1 : GaussianInt) * e + (y.2 : GaussianInt) * f)) -
            TileCentroid (TileTranslation base
              ((x.1 : GaussianInt) * e + (x.2 : GaussianInt) * f)) =
              GaussianRealPoint t
       else
        TileTouching
          (TileTranslation base
            ((x.1 : GaussianInt) * e + (x.2 : GaussianInt) * f))
          (TileTranslation base
            ((y.1 : GaussianInt) * e + (y.2 : GaussianInt) * f))) ↔
        TriangularLatticeAdjacent x y) :
    let u := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
    let v := (⟨0, 1⟩ : GaussianInt) *
      BandVectors.1 (q i.succ) (q ((i + 2).succ))
    ∃ σ : (Int × Int) ≃+ (Int × Int),
      (∀ x y, TriangularLatticeAdjacent (σ x) (σ y) ↔
        TriangularLatticeAdjacent x y) ∧
      (∀ x y z, TriangularSignedHeight (σ x) (σ y) (σ z) =
        TriangularSignedHeight x y z) ∧
      ∃ a b c d : Int,
        ((σ.symm (a, b)).1 : GaussianInt) * e +
            ((σ.symm (a, b)).2 : GaussianInt) * f = u ∧
        ((σ.symm (c, d)).1 : GaussianInt) * e +
            ((σ.symm (c, d)).2 : GaussianInt) * f = v ∧
        0 ≤ b ∧ b ≤ a ∧ 0 ≤ d ∧ d ≤ c ∧
        a * d - b * c = -1 := by
-- BODY
  classical
  let u := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
  let v := (⟨0, 1⟩ : GaussianInt) *
    BandVectors.1 (q i.succ) (q ((i + 2).succ))
  have hu_mem : u ∈ TilingLattice C :=
    (ParentVectorsInTilingLattice q hq i C hC).1
  have hv_mem : v ∈ TilingLattice C := by
    have hit : BandTangency (q i.succ) (q ((i + 2).succ)) := by
      refine ⟨q, hq.1, i.succ, (i + 2).succ, ?_, rfl, rfl⟩
      fin_cases i <;> decide
    have hrev := (ParentVectorsInTilingLattice q hq i C hC).2
    rcases BandVectorOrientationDichotomy _ _ hit with ⟨h, _⟩ | ⟨h, _⟩
    · change (⟨0, 1⟩ : GaussianInt) * _ ∈ _
      rw [h]
      exact hrev
    · change (⟨0, 1⟩ : GaussianInt) * _ ∈ _
      rw [h]
      exact (TilingLattice C).neg_mem hrev
  obtain ⟨p, hp, _⟩ := hcoord ⟨u, hu_mem⟩
  obtain ⟨r, hr, _⟩ := hcoord ⟨v, hv_mem⟩
  have positive : 0 < (q i.succ).1 := by rw [hC]; exact C.2
  have physical_det : u.re * v.im - u.im * v.re = -C.1.1.1 := by
    let s : Fin 4 → CircleCoordinates :=
      ![q 0, q i.succ, q ((i + 1).succ), q ((i + 2).succ)]
    have hs : SemiProperQuadruple s := by
      fin_cases i
      · have eta : (![q 0, q 1, q 2, q 3] : Fin 4 → CircleCoordinates) = q := by
          funext j
          fin_cases j <;> rfl
        simpa [s, eta] using hq.1
      · simpa [s] using SemiProperQuadruple.rotate hq.1
      · simpa [s] using SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1)
    have hspos : 0 < (s 1).1 := by simpa [s] using positive
    have signed := congrArg (fun z : GaussianInt => z.re)
      (VectorDeterminant s hs hspos).1
    rw [← hC]
    simp [s, u, v] at signed ⊢
    ring_nf at signed ⊢
    omega
  have coordinate_det : p.1 * r.2 - p.2 * r.1 = -1 := by
    have covolume := P4994T6ChartCovolume C e f hdet he hf hcoord
    have hpre := congrArg (fun z : GaussianInt => z.re) hp
    have hpim := congrArg (fun z : GaussianInt => z.im) hp
    have hrre := congrArg (fun z : GaussianInt => z.re) hr
    have hrim := congrArg (fun z : GaussianInt => z.im) hr
    simp only [Int.reduceNeg, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero, Zsqrtd.im_add, Zsqrtd.im_mul]
        at hpre hpim hrre hrim
    have factor : u.re * v.im - u.im * v.re =
        (e.re * f.im - e.im * f.re) * (p.1 * r.2 - p.2 * r.1) := by
      rw [← hpre, ← hpim, ← hrre, ← hrim]
      ring
    rw [physical_det, covolume] at factor
    nlinarith
  have common_chamber : ∃ n, P4994T6Chamber n p ∧ P4994T6Chamber n r := by
    by_cases hunit : C.1.1.1 = 1
    · have unit_occurrence : (q i.succ).1 = 1 := by rw [hC]; exact hunit
      obtain ⟨n, _, hpn, hrn⟩ := P4994T6UnitOccurrenceChamber q hq i
        unit_occurrence orientation (horientation unit_occurrence)
      have realPoint_injective : Function.Injective GaussianRealPoint := by
        intro x y hxy
        apply Zsqrtd.ext
        · have h := congrArg Prod.fst hxy
          dsimp [GaussianRealPoint] at h
          exact_mod_cast h
        · have h := congrArg Prod.snd hxy
          dsimp [GaussianRealPoint] at h
          exact_mod_cast h
      have centroid_difference (x y : GaussianInt) :
          TileCentroid (TileTranslation base y) -
            TileCentroid (TileTranslation base x) = GaussianRealPoint (y - x) := by
        rw [(TileTranslationFormulas base y).2.2.2.2.1,
          (TileTranslationFormulas base x).2.2.2.2.1]
        ext <;> simp [GaussianRealPoint]
      have step_of_adj (s : Int × Int) (hs : TriangularLatticeAdjacent 0 s) :
          UnitTriangularStep orientation
            ((s.1 : GaussianInt) * e + (s.2 : GaussianInt) * f) := by
        have h := (hadj 0 s).2 hs
        simp only [hunit, ↓reduceIte] at h
        obtain ⟨t, ht, hcent⟩ := h
        rw [centroid_difference] at hcent
        simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul,
          zero_add, sub_zero] at hcent
        rw [realPoint_injective hcent]
        exact ht
      have e_step : UnitTriangularStep orientation e := by
        simpa using step_of_adj (1, 0) (by simp [TriangularLatticeAdjacent])
      have f_step : UnitTriangularStep orientation f := by
        simpa using step_of_adj (0, 1) (by simp [TriangularLatticeAdjacent])
      have sum_step : UnitTriangularStep orientation (e + f) := by
        simpa using step_of_adj (1, 1) (by simp [TriangularLatticeAdjacent])
      obtain ⟨m, _, alignment⟩ := P4994T6UnitChartRotation orientation e f
        hdet e_step f_step sum_step
      refine ⟨m + n, ?_, ?_⟩
      · unfold P4994T6Chamber at hpn ⊢
        rw [P4994T6RotationLaws.2.2.2 m n p, ← alignment p, hp]
        exact hpn
      · unfold P4994T6Chamber at hrn ⊢
        rw [P4994T6RotationLaws.2.2.2 m n r, ← alignment r, hr]
        exact hrn
    · have touching_chart : ∀ x y : Int × Int,
          TileTouching
            (TileTranslation base ((x.1 : GaussianInt) * e + (x.2 : GaussianInt) * f))
            (TileTranslation base ((y.1 : GaussianInt) * e + (y.2 : GaussianInt) * f)) ↔
          TriangularLatticeAdjacent x y := by
        intro x y
        simpa only [hunit, ↓reduceIte] using hadj x y
      obtain ⟨n, _, hpn, hrn⟩ := P4994T6NonunitChamber q hq C i hC hunit
        base hbase e f hdet he hf hcoord touching_chart p r hp hr
      exact ⟨n, hpn, hrn⟩
  obtain ⟨n, hpn, hrn⟩ := common_chamber
  let σ := P4994T6Rotation n
  refine ⟨σ, P4994T6RotationLaws.1 n, P4994T6RotationLaws.2.1 n,
    (σ p).1, (σ p).2, (σ r).1, (σ r).2, ?_, ?_,
    hpn.1, hpn.2, hrn.1, hrn.2, ?_⟩
  · simpa only [Prod.eta, AddEquiv.symm_apply_apply] using hp
  · simpa only [Prod.eta, AddEquiv.symm_apply_apply] using hr
  · have invariant := P4994T6RotationLaws.2.1 n 0 p r
    have det_invariant : (σ p).1 * (σ r).2 - (σ p).2 * (σ r).1 =
        p.1 * r.2 - p.2 * r.1 := by
      simpa only [map_zero, TriangularSignedHeight, Prod.fst_zero,
        Prod.snd_zero, sub_zero] using invariant
    exact det_invariant.trans coordinate_det

end ApollonianSuperharmonic

end
