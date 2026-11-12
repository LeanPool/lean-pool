/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4994T6StepChamber
public import LeanPool.ApollonianSuperharmonic.P4994T6ChartCovolume
public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification

-- [TABLET NODE: P4994T6NonunitBirth]

/-!
# P4994T6NonunitBirth

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6NonunitBirth :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (C : BandCircle), (q 0 =
        C.1.1) → ((C.1.1.1 ≠ 1) → (∀ (base : ProtoTile), (BandPrototile C.1.1 base) → (∀ (e :
        GaussianInt), ∀ (f : GaussianInt), (0 < e.re * f.im - e.im * f.re) → ((e ∈ TilingLattice
        C) → ((f ∈ TilingLattice C) → ((∀ w : TilingLattice C, ∃! z : Int × Int,
      (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f = (w : GaussianInt)) → ((∀ x y : Int × Int,
      TileTouching
        (TileTranslation base ((x.1 : GaussianInt) * e + (x.2 : GaussianInt) * f))
        (TileTranslation base ((y.1 : GaussianInt) * e + (y.2 : GaussianInt) * f)) ↔
      TriangularLatticeAdjacent x y) → (∀ (p : Int × Int), ∀ (r : Int × Int), ((p.1 :
          GaussianInt) * e + (p.2 : GaussianInt) * f =
      BandVectors.1 (q 2) (q 0)) → (((r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
      -BandVectors.1 (q 3) (q 0)) → (∃ n < 6, P4994T6Chamber n p ∧ P4994T6Chamber n
          r))))))))))) := by
  intro q hq C hC hnonunit base hbase e f hdet he hf hcoord hadj p r hp hr
-- BODY
  let s : Fin 4 → CircleCoordinates :=
    ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
       2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2), q 0, q 2, q 3]
  have hs : SemiProperQuadruple s := SemiProperQuadruple.successor hq.1
  have positive : 0 < (s (0 : Fin 3).succ).1 := by simpa [s, hC] using C.2
  have flip : (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 3) =
      -BandVectors.1 (q 3) (q 0) := by
    have hf := ((VectorRecursionLaws q hq.1).2.2.2.2 hq 2).1
    change BandVectors.1 (q 0) (q 3) =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 0) at hf
    rw [hf]
    ext <;> simp
  have signed : (BandVectors.1 (q 2) (q 0)).re *
      ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 3)).im -
    (BandVectors.1 (q 2) (q 0)).im *
      ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 0) (q 3)).re = -(q 0).1 := by
    have real_part := congrArg (fun z : GaussianInt => z.re)
      (VectorDeterminant s hs positive).1
    simp [s] at real_part ⊢
    ring_nf at real_part ⊢
    omega
  rw [flip] at signed
  have det_coordinates : p.1 * r.2 - p.2 * r.1 = -1 := by
    have covolume := P4994T6ChartCovolume C e f hdet he hf hcoord
    have hpre := congrArg (fun z : GaussianInt => z.re) hp
    have hpim := congrArg (fun z : GaussianInt => z.im) hp
    have hrre := congrArg (fun z : GaussianInt => z.re) hr
    have hrim := congrArg (fun z : GaussianInt => z.im) hr
    simp only [Int.reduceNeg, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero, Fin.isValue, Zsqrtd.im_add,
        Zsqrtd.im_mul, Zsqrtd.re_neg, Zsqrtd.im_neg] at hpre hpim hrre hrim
    have factor :
        (BandVectors.1 (q 2) (q 0)).re * (-BandVectors.1 (q 3) (q 0)).im -
          (BandVectors.1 (q 2) (q 0)).im * (-BandVectors.1 (q 3) (q 0)).re =
        (e.re * f.im - e.im * f.re) * (p.1 * r.2 - p.2 * r.1) := by
      simp only [Zsqrtd.re_neg, Zsqrtd.im_neg]
      rw [← hpre, ← hpim, ← hrre, ← hrim]
      ring
    rw [signed, hC, covolume] at factor
    have positive_curvature := C.2
    nlinarith
  have steps : TriangularLatticeAdjacent 0 p ∧
      TriangularLatticeAdjacent 0 r ∧ TriangularLatticeAdjacent p r := by
    let chart : Int × Int → GaussianInt := fun z =>
      (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f
    have in_family (z : Int × Int) :
        TileTranslation base (chart z) ∈ RegularTileFamily base (TilingLattice C) := by
      refine ⟨chart z, ?_, rfl⟩
      simpa only [chart, zsmul_eq_mul] using (TilingLattice C).add_mem
        ((TilingLattice C).zsmul_mem he z.1) ((TilingLattice C).zsmul_mem hf z.2)
    have centroid_difference (x y : GaussianInt) :
        TileCentroid (TileTranslation base y) -
          TileCentroid (TileTranslation base x) = GaussianRealPoint (y - x) := by
      rw [(TileTranslationFormulas base y).2.2.2.2.1,
        (TileTranslationFormulas base x).2.2.2.2.1]
      ext <;> simp [GaussianRealPoint]
    have edge (x y : Int × Int) (j : Fin 3)
        (hxy : chart y - chart x = BandVectors.1 (q j.succ) (q 0) ∨
          chart y - chart x = -BandVectors.1 (q j.succ) (q 0)) :
        TriangularLatticeAdjacent x y := by
      apply (hadj x y).mp
      apply (BandRegularTileTouchingClassification C q hq hC base
        (by simpa only [hC] using hbase) _ _ (in_family x) (in_family y)).2
      refine ⟨j, ?_⟩
      rw [centroid_difference]
      rcases hxy with positive | negative
      · exact Or.inl (congrArg GaussianRealPoint positive)
      · right
        rw [negative]
        ext <;> simp [GaussianRealPoint]
    have incoming := (IncomingSuperbasisRelation q hq).1
    have sum : BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
        BandVectors.1 (q 3) (q 0) = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using incoming
    have first_eq : BandVectors.1 (q 1) (q 0) =
        -(BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0)) :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using sum)
    refine ⟨edge 0 p 1 (Or.inl ?_), edge 0 r 2 (Or.inr ?_),
      edge p r 0 (Or.inl ?_)⟩
    · simpa [chart] using hp
    · simpa [chart] using hr
    · change ((r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f) -
          ((p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f) =
          BandVectors.1 (q 1) (q 0)
      rw [hp, hr, first_eq]
      ring
  exact P4994T6StepChamber p r steps.1 steps.2.1 steps.2.2 det_coordinates

end ApollonianSuperharmonic

end
