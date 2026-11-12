/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4261T2UnitBoundary
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.P4250T1DefinedHalfIntegralSlope
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.RegularTileFamilyTranslationUnique

-- [TABLET NODE: P4261T2RegularEdgeReduction]

/-!
# P4261T2RegularEdgeReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2RegularEdgeReduction
    (C : BandCircle) (base U V : ProtoTile)
    (hbase : BandPrototile C.1.1 base)
    (hU : U ∈ RegularTileFamily base (TilingLattice C))
    (hV : V ∈ RegularTileFamily base (TilingLattice C))
    (g k : PartialOdometer) (hg : TileOdometer C.1.1 U g)
    (hk : TileOdometer C.1.1 V k)
    (s t : Real × Real)
    (hs : PartialOdometerSlope g = some s) (ht : PartialOdometerSlope k = some t)
    (h0 : t.1 - s.1 = CircleMatrix C 0 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
      CircleMatrix C 0 1 * ((TileCentroid V).2 - (TileCentroid U).2))
    (h1 : t.2 - s.2 = CircleMatrix C 1 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
      CircleMatrix C 1 1 * ((TileCentroid V).2 - (TileCentroid U).2))
    (hedge : (FootprintEdges U ∩ FootprintEdges V).Nonempty) :
    OdometerCompatibility g k ∨ LeftLatticeAdjacent C U V g k := by
-- BODY
  classical
  by_cases hunit : C.1.1.1 = 1
  · exact Or.inl (P4261T2UnitBoundary C hunit U V g k hg hk s t hs ht h0 h1)
  by_cases heq : U = V
  · subst V
    obtain ⟨_, _, _, _, hnonempty⟩ :=
      P4250T1DefinedHalfIntegralSlope C.1.1 U g C.2 hg
    obtain ⟨w, ⟨hcells, hanchor, a, b, hd, hv⟩, _⟩ :=
      TileOdometerTranslationUniqueness C.1.1 U U g k C.2 hg hk
    have hcne : (U.cells.card : Int) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hnonempty
    have hwre : w.re = 0 := by
      have he := congrArg (fun S : Finset GaussianInt => ∑ z ∈ S, z.re) hcells
      simp only [TileTranslation] at he
      rw [Finset.sum_image (by
        intro x hx y hy hxy
        exact add_right_cancel hxy)] at he
      simp only [GaussianTranslation, Zsqrtd.re_add, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul] at he
      have hz : (U.cells.card : Int) * w.re = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left hcne
    have hwim : w.im = 0 := by
      have he := congrArg (fun S : Finset GaussianInt => ∑ z ∈ S, z.im) hcells
      simp only [TileTranslation] at he
      rw [Finset.sum_image (by
        intro x hx y hy hxy
        exact add_right_cancel hxy)] at he
      simp only [GaussianTranslation, Zsqrtd.im_add, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul] at he
      have hz : (U.cells.card : Int) * w.im = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left hcne
    have hw : w = 0 := Zsqrtd.ext hwre hwim
    subst w
    have hh : g.domain = (PartialOdometerAffineTranslate k 0 a b).domain := by
      ext x
      rw [(PartialOdometerAffineTranslateFormulas k 0 a b).2.1]
      exact hd x
    have hvalue : g.value = (PartialOdometerAffineTranslate k 0 a b).value := by
      funext x
      by_cases hx : x ∈ g.domain
      · rw [hv x hx, (PartialOdometerAffineTranslateFormulas k 0 a b).2.2.1 x
          (by rwa [← hh])]
      · rw [g.value_outside x hx,
          (PartialOdometerAffineTranslate k 0 a b).value_outside x (by rwa [← hh])]
    have heq : g = PartialOdometerAffineTranslate k 0 a b := by
      cases g
      simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
      exact ⟨hh, hvalue⟩
    have hep := congrArg PartialOdometerSlope heq
    rw [hs, (PartialOdometerAffineTranslateFormulas k 0 a b).2.2.2.2.2, ht] at hep
    have hep' := Option.some.inj hep
    have hare : a.re = 0 := by
      have he := congrArg Prod.fst hep'
      change s.1 = t.1 + (a.re : Real) at he
      have hzero : t.1 - s.1 = 0 := by simpa using h0
      exact_mod_cast (show (a.re : Real) = 0 by linarith)
    have haim : a.im = 0 := by
      have he := congrArg Prod.snd hep'
      change s.2 = t.2 + (a.im : Real) at he
      have hzero : t.2 - s.2 = 0 := by simpa using h1
      exact_mod_cast (show (a.im : Real) = 0 by linarith)
    left
    right
    refine ⟨-b, ?_⟩
    intro x hx hx'
    have hvx := hv x hx
    simp only [sub_zero, hare, haim, zero_mul, add_zero] at hvx
    omega
  obtain ⟨q, hsemi, hqC, hsmall, _⟩ := (BandGenealogy C).resolve_left hunit
  have hq : ProperBandQuadruple q := ⟨hsemi, by simpa only [hqC] using hsmall⟩
  obtain ⟨u, hu, _⟩ := RegularTileFamilyTranslationUnique base (TilingLattice C) U hU
  obtain ⟨v, hv, _⟩ := RegularTileFamilyTranslationUnique base (TilingLattice C) V hV
  obtain ⟨P, _, htiles, hadj, _⟩ := BandRegularTranslatePeriodicComplex C q hq hqC base
    (by simpa only [hqC] using hbase)
  have hne : u ≠ v := by
    intro huv
    apply heq
    rw [hu, hv, huv]
  have hedgeP : (FootprintEdges (P.tile u) ∩ FootprintEdges (P.tile v)).Nonempty := by
    simpa only [htiles, ← hu, ← hv] using hedge
  have hcontact := ((PeriodicTileIntersectionClassification P).1 u v hne).1.mp hedgeP
  have hcent : TileCentroid V - TileCentroid U =
      GaussianRealPoint ((v : GaussianInt) - (u : GaussianInt)) := by
    rw [hu, hv, (TileTranslationFormulas base v).2.2.2.2.1,
      (TileTranslationFormulas base u).2.2.2.2.1]
    apply Prod.ext <;> simp [GaussianRealPoint]
  have finish (j : Fin 3) (e : Bool)
      (hc : TileCentroid V - TileCentroid U =
        (if e = true then (1 : Real) else -1) •
          GaussianRealPoint (BandVectors.1 (q j.succ) (q 0))) :
      LeftLatticeAdjacent C U V g k := by
    have hin := CircleMatrixIncomingVector C q hq.1 hqC j
    have hin0 := congrFun hin 0
    have hin1 := congrFun hin 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hin0 hin1
    have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    change (TileCentroid V).1 - (TileCentroid U).1 =
      (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).re : Real) at hc0
    change (TileCentroid V).2 - (TileCentroid U).2 =
      (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).im : Real) at hc1
    refine ⟨hg, hk, s, t, hs, ht, Or.inr ⟨q, j, e, hq, hqC, hc, ?_, ?_⟩⟩
    · rw [hc0, hc1] at h0
      linear_combination h0 + (if e = true then (1 : Real) else -1) * hin0
    · rw [hc0, hc1] at h1
      linear_combination h1 + (if e = true then (1 : Real) else -1) * hin1
  right
  obtain ⟨j, hj | hj⟩ := (hadj u v).mp hcontact
  · apply finish j true
    simpa [hj] using hcent
  · apply finish j false
    simpa [hj, GaussianRealPoint] using hcent

end ApollonianSuperharmonic

end
