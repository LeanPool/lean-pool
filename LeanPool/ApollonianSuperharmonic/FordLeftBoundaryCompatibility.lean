/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: FordLeftBoundaryCompatibility]

/-!
# FordLeftBoundaryCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordBoundaryCompatibilityGeometry

private theorem hcurv :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (r0 : Fin (3 : ℕ)), ∀ (g0 : BandPackingSymmetry), ∀
            (P0 : FordFareyParameter), ((1 : ℕ) < P0.q) → ((BandPackingSymmetryQuadrupleAction g0
            ![q (0 : Fin (4 : ℕ)), q r0.succ, q (r0 + (1 : Fin (3 : ℕ))).succ, q (r0 + (2 : Fin
            (3 : ℕ))).succ] = FordRecursiveQuadruple P0) → (1 < (q 0).1)) ) := by
  classical
  intro q r0 g0 P0 hP0 heq0
  have hc := (BandPackingSymmetryCovariance g0).1 (q 0)
  have he := congrFun heq0 0
  have hecurv := congrArg Prod.fst he
  simp only [BandPackingSymmetryQuadrupleAction, Fin.isValue, Matrix.cons_val_zero, neg_zero,
      ite_self, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_succ] at hecurv
  rw [hc] at hecurv
  have hqp : (1 : ℝ) < P0.q := by exact_mod_cast hP0
  simp [FordRecursiveQuadruple, FordCircleCoordinate] at hecurv
  nlinarith

private theorem iline0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (1 < (q 0).1) → (∀ (iline : Fin (4 : ℕ)), ((q
            iline).1 = (0 : ℤ)) → (iline ≠ 0)) ) := by
  classical
  intro q hcurv iline hiline hz
  subst iline
  linarith [hcurv, hiline]

private theorem wline :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (r1 : Fin
            (3 : ℕ)), (∀ (j : Fin (3 : ℕ)), w j.succ = q (j + r1).succ) → ((∀ (y : Fin (3 : ℕ)),
            (fun (r : Fin (3 : ℕ)) => ∀ (j : Fin (3 : ℕ)), w j.succ = q (j + r).succ) y → y = r1)
            → (∀ (iline : Fin (4 : ℕ)), ((q iline).1 = (0 : ℤ)) → ((iline ≠ 0) → (∃ j : Fin 4, (w
            j).1 = 0)))) ) := by
  classical
  intro q w r1 hr1 hruniq iline hiline iline0
  refine ⟨(iline.pred iline0 - r1).succ, ?_⟩
  simpa only [hr1, sub_add_cancel, Fin.succ_pred] using hiline

private theorem hbar :
    (by
      classical
      exact
        ∀ (w : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple w) → (∀ (r2 : Fin (3 : ℕ)),
            ∀ (g2 : BandPackingSymmetry), ∀ (P2 : FordFareyParameter), ((w (r2 + (2 : Fin (3 :
            ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g2 ![w (0 : Fin (4 :
            ℕ)), w r2.succ, w (r2 + (1 : Fin (3 : ℕ))).succ, w (r2 + (2 : Fin (3 : ℕ))).succ] =
            FordRecursiveQuadruple P2) → (
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        ProperBandQuadruple barq))) ) := by
  classical
  intro w hwproper r2 g2 P2 hz2 heq2 barq
  fin_cases r2
  · exact ⟨by
      convert hwproper.1 using 1; funext j; fin_cases j <;> rfl, by
      intro j
      fin_cases j
      · change (w 1).1 < (w 0).1; exact hwproper.2 0
      · change (w 2).1 < (w 0).1; exact hwproper.2 1
      · change (w 3).1 < (w 0).1; exact hwproper.2 2⟩
  · exact ⟨SemiProperQuadruple.rotate hwproper.1, by
      intro j
      fin_cases j
      · simpa [barq] using hwproper.2 1
      · simpa [barq] using hwproper.2 2
      · simpa [barq] using hwproper.2 0⟩
  · exact ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hwproper.1), by
      intro j
      fin_cases j
      · simpa [barq] using hwproper.2 2
      · simpa [barq] using hwproper.2 0
      · simpa [barq] using hwproper.2 1⟩

private theorem hpoint :
    (by
      classical
      exact
        ∀ (w : Fin (4 : ℕ) → CircleCoordinates)
          (iw r2 : Fin (3 : ℕ)),
          let barq :=
            ![w (0 : Fin (4 : ℕ)), w r2.succ, w (r2 + (1 : Fin (3 : ℕ))).succ,
              w (r2 + (2 : Fin (3 : ℕ))).succ];
          ∀ (t : Fin (3 : ℕ)), t + r2 = iw → barq t.succ = w iw.succ) := by
  classical
  intro w iw r2 barq t ht
  revert ht
  fin_cases r2 <;> fin_cases t <;> fin_cases iw <;> simp [barq]

private theorem hcentbar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (q : Fin 4 ->
            CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) → (∀ (w : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (iw : Fin (3 : ℕ)), ∀ (ew : Bool), (w (0 : Fin (4 : ℕ)) =
            C.1.1) → ((TileCentroid T' - TileCentroid T = (if ew = true then (1 : ℝ) else (-1 :
            ℝ)) • GaussianRealPoint (BandVectors.1 (w iw.succ) (w (0 : Fin (4 : ℕ))))) → (∀ (r2 :
            Fin (3 : ℕ)),
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        (barq 0 = q 0) → (∀ (t : Fin (3 : ℕ)), (barq t.succ = w iw.succ) → (TileCentroid T' -
            TileCentroid T = (if ew = true then (1 : ℝ) else -1) • GaussianRealPoint
            (BandVectors.1 (barq t.succ) (barq 0))))))) ) := by
  classical
  intro C T T' q hC w iw ew hwchild hwcent r2 barq hbar0 t hpoint
  rw [hpoint, hbar0, hC]
  simpa [hwchild] using hwcent

private theorem hslopebar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 -> CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) →
            (∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (iw : Fin
            (3 : ℕ)), ∀ (ew : Bool), (w (0 : Fin (4 : ℕ)) = C.1.1) → ((p'.1 - p.1 = (if ew = true
            then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (w iw.succ) (w (0 : Fin (4 : ℕ)))).re
            : ℝ)) → (∀ (r2 : Fin (3 : ℕ)),
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        (barq 0 = q 0) → (∀ (t : Fin (3 : ℕ)), (barq t.succ = w iw.succ) → (p'.1 - p.1 = (if ew =
            true then (1 : ℝ) else -1) * (BandVectors.2 (barq t.succ) (barq 0)).re))))) ) := by
  classical
  intro C q hC p p' w iw ew hwchild hwslope r2 barq hbar0 t hpoint
  rw [hpoint, hbar0, hC]
  simpa [hwchild] using hwslope

private theorem hslopebar' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 -> CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) →
            (∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (iw : Fin
            (3 : ℕ)), ∀ (ew : Bool), (w (0 : Fin (4 : ℕ)) = C.1.1) → ((p'.2 - p.2 = (if ew = true
            then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (w iw.succ) (w (0 : Fin (4 : ℕ)))).im
            : ℝ)) → (∀ (r2 : Fin (3 : ℕ)),
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        (barq 0 = q 0) → (∀ (t : Fin (3 : ℕ)), (barq t.succ = w iw.succ) → (p'.2 - p.2 = (if ew =
            true then (1 : ℝ) else -1) * (BandVectors.2 (barq t.succ) (barq 0)).im))))) ) := by
  classical
  intro C q hC p p' w iw ew hwchild hwslope' r2 barq hbar0 t hpoint
  rw [hpoint, hbar0, hC]
  simpa [hwchild] using hwslope'

private theorem hCpos :
    (by
      classical
      exact
        ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (r2 : Fin (3 : ℕ)), ∀ (g2 :
            BandPackingSymmetry), ∀ (P2 : FordFareyParameter), ((1 : ℕ) < P2.q) → (
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        (BandPackingSymmetryQuadrupleAction g2 ![w (0 : Fin (4 : ℕ)), w r2.succ, w (r2 + (1 : Fin
            (3 : ℕ))).succ, w (r2 + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)) =
            FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) → (0 <
            (BandPackingSymmetryQuadrupleAction g2 barq 0).1)) ) := by
  classical
  intro w r2 g2 P2 hP2 barq heq0'
  have hqpos : (0 : ℝ) < P2.q := by exact_mod_cast P2.q_pos
  have hh := congrArg Prod.fst heq0'
  simp [FordRecursiveQuadruple, FordCircleCoordinate] at hh
  nlinarith

private theorem hkO' :
    (by
      classical
      exact
        ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (r2 : Fin (3 : ℕ)), ∀ (g2 :
            BandPackingSymmetry), ∀ (P2 : FordFareyParameter),
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        (BandPackingSymmetryQuadrupleAction g2 ![w (0 : Fin (4 : ℕ)), w r2.succ, w (r2 + (1 : Fin
            (3 : ℕ))).succ, w (r2 + (2 : Fin (3 : ℕ))).succ] (0 : Fin (4 : ℕ)) =
            FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) → (∀ (k : PartialOdometer),
            (TileOdometer (FordCircleCoordinate P2.p P2.q) (FordTile P2.q) k) → (TileOdometer
            (BandPackingSymmetryQuadrupleAction g2 barq 0) (FordTile P2.q) k)) ) := by
  classical
  intro w r2 g2 P2 barq heq0' k hkO
  rw [heq0']
  exact hkO

private theorem hcentT :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g2 : BandPackingSymmetry), ∀ (P2 : FordFareyParameter), ∀ (u :
            GaussianInt), ((BandPackingSymmetryTileAction g2 T).cells = (TileTranslation
            (FordTile P2.q) u).cells) → (((BandPackingSymmetryTileAction g2 T).cells = ∅ →
            (BandPackingSymmetryTileAction g2 T).anchor = (TileTranslation (FordTile P2.q)
            u).anchor) → (TileCentroid (BandPackingSymmetryTileAction g2 T) = TileCentroid
            (TileTranslation (FordTile P2.q) u))) ) := by
  classical
  intro T g2 P2 u hu huempty
  rw [TileCentroid, TileCentroid]
  by_cases hn : (BandPackingSymmetryTileAction g2 T).cells.Nonempty
  · have hn' : (TileTranslation (FordTile P2.q) u).cells.Nonempty := by
      rw [← hu]
      exact hn
    simp [hu, hn']
  · have he : (BandPackingSymmetryTileAction g2 T).cells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hn
    have ha := huempty he
    rw [(TileTranslationFormulas (FordTile P2.q) u).2.1] at ha
    have ht : ¬ (TileTranslation (FordTile P2.q) u).cells.Nonempty := by
      simpa [hu] using hn
    simp only [hn, ht, ite_false]
    rw [(TileTranslationFormulas (FordTile P2.q) u).2.1]
    apply Prod.ext
    · change ((BandPackingSymmetryTileAction g2 T).anchor.re : ℝ) =
        ((GaussianTranslation u (FordTile P2.q).anchor).re : ℝ)
      exact_mod_cast congrArg (fun z => z.re) ha
    · change ((BandPackingSymmetryTileAction g2 T).anchor.im : ℝ) =
        ((GaussianTranslation u (FordTile P2.q).anchor).im : ℝ)
      exact_mod_cast congrArg (fun z => z.im) ha

private theorem hcentT' :
    (by
      classical
      exact
        ∀ (T' : ProtoTile), ∀ (g2 : BandPackingSymmetry), ∀ (P2 : FordFareyParameter), ∀ (u' :
            GaussianInt), ((BandPackingSymmetryTileAction g2 T').cells = (TileTranslation
            (FordTile P2.q) u').cells) → (((BandPackingSymmetryTileAction g2 T').cells = ∅ →
            (BandPackingSymmetryTileAction g2 T').anchor = (TileTranslation (FordTile P2.q)
            u').anchor) → (TileCentroid (BandPackingSymmetryTileAction g2 T') = TileCentroid
            (TileTranslation (FordTile P2.q) u'))) ) := by
  classical
  intro T' g2 P2 u' hu' huempty'
  rw [TileCentroid, TileCentroid]
  by_cases hn : (BandPackingSymmetryTileAction g2 T').cells.Nonempty
  · have hn' : (TileTranslation (FordTile P2.q) u').cells.Nonempty := by
      rw [← hu']
      exact hn
    simp [hu', hn']
  · have he : (BandPackingSymmetryTileAction g2 T').cells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hn
    have ha := huempty' he
    rw [(TileTranslationFormulas (FordTile P2.q) u').2.1] at ha
    have ht : ¬ (TileTranslation (FordTile P2.q) u').cells.Nonempty := by
      simpa [hu'] using hn
    simp only [hn, ht, ite_false]
    rw [(TileTranslationFormulas (FordTile P2.q) u').2.1]
    apply Prod.ext
    · change ((BandPackingSymmetryTileAction g2 T').anchor.re : ℝ) =
        ((GaussianTranslation u' (FordTile P2.q).anchor).re : ℝ)
      exact_mod_cast congrArg (fun z => z.re) ha
    · change ((BandPackingSymmetryTileAction g2 T').anchor.im : ℝ) =
        ((GaussianTranslation u' (FordTile P2.q).anchor).im : ℝ)
      exact_mod_cast congrArg (fun z => z.im) ha

private theorem hshift :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (ew :
            Bool), ∀ (r2 : Fin (3 : ℕ)), ∀ (g2 : BandPackingSymmetry), ∀ (P2 :
            FordFareyParameter), (BandPackingSymmetryReversesOrientation g2 = false) → (
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        ∀ (t : Fin (3 : ℕ)), ∀ (negative : Bool), (TileCentroid (BandPackingSymmetryTileAction g2
            T') - TileCentroid (BandPackingSymmetryTileAction g2 T) = (if (ew ^^ negative) = true
            then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g2 barq ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g2 = true then -j else j) t).succ)
            (BandPackingSymmetryQuadrupleAction g2 barq (0 : Fin (4 : ℕ))))) → (∀ (u :
            GaussianInt), ∀ (u' : GaussianInt), (TileCentroid (BandPackingSymmetryTileAction g2
            T) = TileCentroid (TileTranslation (FordTile P2.q) u)) → ((TileCentroid
            (BandPackingSymmetryTileAction g2 T') = TileCentroid (TileTranslation (FordTile P2.q)
            u')) → (u' - u = (if ew ^^ negative then 1 else -1) • BandVectors.1
            (BandPackingSymmetryQuadrupleAction g2 barq t.succ)
            (BandPackingSymmetryQuadrupleAction g2 barq 0))))) ) := by
  classical
  intro T T' w ew r2 g2 P2 hg2 barq t negative hcent' u u' hcentT hcentT'
  have hc := congrArg Prod.fst hcent'
  rw [hcentT, hcentT'] at hc
  rw [(TileTranslationFormulas (FordTile P2.q) u).2.2.2.2.1,
    (TileTranslationFormulas (FordTile P2.q) u').2.2.2.2.1] at hc
  have hc2 := congrArg Prod.snd hcent'
  rw [hcentT, hcentT'] at hc2
  rw [(TileTranslationFormulas (FordTile P2.q) u).2.2.2.2.1,
    (TileTranslationFormulas (FordTile P2.q) u').2.2.2.2.1] at hc2
  simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk_sub_mk,
      add_sub_add_left_eq_sub, bne_iff_ne, ne_eq, ite_not, hg2, Bool.false_eq_true,
      ↓reduceIte, Fin.isValue, ite_smul, neg_smul, one_smul] at hc hc2
  by_cases hs : ew = negative
  · simp only [hs, ↓reduceIte, Fin.isValue, Prod.fst_neg, Prod.snd_neg, bne_self_eq_false,
      Bool.false_eq_true, Int.reduceNeg, neg_smul, one_smul] at hc hc2 ⊢
    unfold GaussianRealPoint at hc hc2
    simp only [GaussianInt.toComplex, Zsqrtd.lift_apply_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
      zero_add, mul_one] at hc hc2
    ring_nf at hc hc2
    apply Zsqrtd.ext
    · dsimp at hc ⊢
      exact_mod_cast hc
    · dsimp at hc2 ⊢
      exact_mod_cast hc2
  · simp only [hs, ↓reduceIte, Fin.isValue, bne_iff_ne, ne_eq, not_false_eq_true, one_smul]
      at hc hc2 ⊢
    unfold GaussianRealPoint at hc hc2
    simp only [GaussianInt.toComplex, Zsqrtd.lift_apply_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
      zero_add, mul_one] at hc hc2
    ring_nf at hc hc2
    apply Zsqrtd.ext
    · dsimp at hc ⊢
      exact_mod_cast hc
    · dsimp at hc2 ⊢
      exact_mod_cast hc2

private theorem heqH :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (g2 : BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (u :
            GaussianInt), ∀ (a : GaussianInt), ∀ (b : ℤ), (∀ (x : GaussianInt), x ∈
            (BandPackingSymmetryPartialOdometerAction g2 h).domain ↔ x - u ∈ k.domain) → ((∀ x ∈
            (BandPackingSymmetryPartialOdometerAction g2 h).domain,
            (BandPackingSymmetryPartialOdometerAction g2 h).value x = k.value (x - u) + a.re *
            x.re + a.im * x.im + b) → (BandPackingSymmetryPartialOdometerAction g2 h =
            PartialOdometerAffineTranslate k u a b)) ) := by
  classical
  intro h g2 k u a b hud huv
  apply (PartialOdometer.mk.injEq _ _ _ _ _ _).mpr
  constructor
  · apply Finset.ext
    intro x
    exact (hud x).trans ((PartialOdometerAffineTranslateFormulas k u a b).2.1 x).symm
  · apply funext
    intro x
    change (BandPackingSymmetryPartialOdometerAction g2 h).value x =
      (PartialOdometerAffineTranslate k u a b).value x
    by_cases hx : x ∈ (BandPackingSymmetryPartialOdometerAction g2 h).domain
    · rw [(PartialOdometerAffineTranslateFormulas k u a b).2.2.1 x
          (by
            have hxa := (PartialOdometerAffineTranslateFormulas k u a b).2.1 x
            exact hxa.mpr ((hud x).mp hx))]
      exact huv x hx
    · have hxa := (PartialOdometerAffineTranslateFormulas k u a b).2.1 x
      have hnot : x ∉ (PartialOdometerAffineTranslate k u a b).domain := by
        intro ha
        exact hx ((hud x).mpr (hxa.mp ha))
      rw [(BandPackingSymmetryPartialOdometerAction g2 h).value_outside x hx,
        (PartialOdometerAffineTranslate k u a b).value_outside x hnot]

private theorem heqH' :
    (by
      classical
      exact
        ∀ (h' : PartialOdometer), ∀ (g2 : BandPackingSymmetry), ∀ (k : PartialOdometer), ∀ (u' :
            GaussianInt), ∀ (a' : GaussianInt), ∀ (b' : ℤ), (∀ (x : GaussianInt), x ∈
            (BandPackingSymmetryPartialOdometerAction g2 h').domain ↔ x - u' ∈ k.domain) → ((∀ x
            ∈ (BandPackingSymmetryPartialOdometerAction g2 h').domain,
            (BandPackingSymmetryPartialOdometerAction g2 h').value x = k.value (x - u') + a'.re *
            x.re + a'.im * x.im + b') → (BandPackingSymmetryPartialOdometerAction g2 h' =
            PartialOdometerAffineTranslate k u' a' b')) ) := by
  classical
  intro h' g2 k u' a' b' hud' huv'
  apply (PartialOdometer.mk.injEq _ _ _ _ _ _).mpr
  constructor
  · apply Finset.ext
    intro x
    exact (hud' x).trans ((PartialOdometerAffineTranslateFormulas k u' a' b').2.1 x).symm
  · apply funext
    intro x
    change (BandPackingSymmetryPartialOdometerAction g2 h').value x =
      (PartialOdometerAffineTranslate k u' a' b').value x
    by_cases hx : x ∈ (BandPackingSymmetryPartialOdometerAction g2 h').domain
    · rw [(PartialOdometerAffineTranslateFormulas k u' a' b').2.2.1 x
          (by
            have hxa := (PartialOdometerAffineTranslateFormulas k u' a' b').2.1 x
            exact hxa.mpr ((hud' x).mp hx))]
      exact huv' x hx
    · have hxa := (PartialOdometerAffineTranslateFormulas k u' a' b').2.1 x
      have hnot : x ∉ (PartialOdometerAffineTranslate k u' a' b').domain := by
        intro ha
        exact hx ((hud' x).mpr (hxa.mp ha))
      rw [(BandPackingSymmetryPartialOdometerAction g2 h').value_outside x hx,
        (PartialOdometerAffineTranslate k u' a' b').value_outside x hnot]

private theorem hvec :
    (by
      classical
      exact
        ∀ (w : Fin (4 : ℕ) → CircleCoordinates), ∀ (ew : Bool), ∀ (r2 : Fin (3 : ℕ)), ∀ (g2 :
            BandPackingSymmetry), ∀ (P2 : FordFareyParameter),
            (BandPackingSymmetryQuadrupleAction g2 ![w (0 : Fin (4 : ℕ)), w r2.succ, w (r2 + (1 :
            Fin (3 : ℕ))).succ, w (r2 + (2 : Fin (3 : ℕ))).succ] = FordRecursiveQuadruple P2) → (
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        ∀ (t : Fin (3 : ℕ)), ∀ (negative : Bool), ∀ (u : GaussianInt), ∀ (u' : GaussianInt), (u'
            - u = (if ew ^^ negative then 1 else -1) • BandVectors.1
            (BandPackingSymmetryQuadrupleAction g2 barq t.succ)
            (BandPackingSymmetryQuadrupleAction g2 barq 0)) → (u' - u = (if (ew ^^ negative) =
            true then 1 else -1) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 0))) ) := by
  classical
  intro w ew r2 g2 P2 heq2 barq t negative u u' hshift
  rw [heq2] at hshift
  simpa using hshift

private theorem haRe :
    (by
      classical
        exact
        ∀ (ew : Bool),
          (∀ (P2 : FordFareyParameter),
            ∀ (t : Fin (3 : ℕ)),
              (∀ (negative : Bool),
                ∀ (r : ℝ × ℝ),
                  ∀ (r' : ℝ × ℝ),
                    (∀ (a : GaussianInt),
                      ∀ (a' : GaussianInt),
                        (∀ (z : ℝ × ℝ),
                          (r'.1 - r.1 =
                              if ew = negative then
                                -((↑(BandVectors.2
                                            (FordRecursiveQuadruple P2 t.succ)
                                            (FordRecursiveQuadruple P2
                                              (0 : Fin (4 : ℕ)))).re :
                                      ℝ) +
                                    ((↑(BandVectors.2
                                                (FordRecursiveQuadruple P2 t.succ)
                                                (FordRecursiveQuadruple P2
                                                  (0 : Fin (4 : ℕ)))).im :
                                          ℝ) *
                                        (0 : ℝ) -
                                      (0 : ℝ)))
                              else
                                (↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
                                          (FordRecursiveQuadruple P2
                                            (0 : Fin (4 : ℕ)))).re :
                                    ℝ) +
                                  ((↑(BandVectors.2
                                              (FordRecursiveQuadruple P2 t.succ)
                                              (FordRecursiveQuadruple P2
                                                (0 : Fin (4 : ℕ)))).im :
                                        ℝ) *
                                      (0 : ℝ) -
                                    (0 : ℝ))) →
                            ((r.1 =
                                z.1 +
                                  ((↑a.re : ℝ) +
                                    ((↑a.im : ℝ) * (0 : ℝ) - (0 : ℝ)))) →
                              ((r'.1 =
                                  z.1 +
                                    ((↑a'.re : ℝ) +
                                      ((↑a'.im : ℝ) * (0 : ℝ) - (0 : ℝ)))) →
                                (a'.re - a.re =
                                  (if (ew ^^ negative) = true then 1 else -1) *
                                    (BandVectors.2
                                        (FordRecursiveQuadruple P2 t.succ)
                                        (FordRecursiveQuadruple P2 0)).re)))))))) := by
  classical
  intro ew P2 t negative r r' a a' z hsreFord sr sr'
  fin_cases t <;> cases ew <;> cases negative
  all_goals
    simp only [Bool.xor_true, Bool.xor_false,
      ite_true] at sr sr' hsreFord ⊢
    have slopeDifference : r'.1 - r.1 = (a'.re : ℝ) - a.re := by
      linarith [sr, sr']
    have transformedDifference := hsreFord
    rw [slopeDifference] at transformedDifference
    try
    norm_num at transformedDifference ⊢
    try simp only [← GaussianInt.intCast_re] at transformedDifference
    exact_mod_cast transformedDifference

private theorem haIm :
    (by
      classical
        exact
        ∀ (ew : Bool),
          (∀ (P2 : FordFareyParameter),
            ∀ (t : Fin (3 : ℕ)),
              (∀ (negative : Bool),
                ∀ (r : ℝ × ℝ),
                  ∀ (r' : ℝ × ℝ),
                    (∀ (a : GaussianInt),
                      ∀ (a' : GaussianInt),
                        (∀ (z : ℝ × ℝ),
                          ((r'.2 - r.2 =
                              if ew = negative then
                                -(↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
                                          (FordRecursiveQuadruple P2
                                            (0 : Fin (4 : ℕ)))).im :
                                    ℝ)
                              else
                                (↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
                                        (FordRecursiveQuadruple P2
                                          (0 : Fin (4 : ℕ)))).im :
                                  ℝ)) →
                            ((r.2 = z.2 + (↑a.im : ℝ)) →
                              ((r'.2 = z.2 + (↑a'.im : ℝ)) →
                                (a'.im - a.im =
                                  (if (ew ^^ negative) = true then 1 else -1) *
                                    (BandVectors.2
                                        (FordRecursiveQuadruple P2 t.succ)
                                        (FordRecursiveQuadruple P2 0)).im))))))))) := by
  classical
  intro ew P2 t negative r r' a a' z hsimFord si si'
  fin_cases t <;> cases ew <;> cases negative
  all_goals
    simp only [Bool.xor_true, Bool.xor_false,
      ite_true] at si si' hsimFord ⊢
    have slopeDifference : r'.2 - r.2 = (a'.im : ℝ) - a.im := by
      linarith [si, si']
    have transformedDifference := hsimFord
    rw [slopeDifference] at transformedDifference
    try
    norm_num at transformedDifference ⊢
    try simp only [← GaussianInt.intCast_im] at transformedDifference
    exact_mod_cast transformedDifference

private theorem hcoc :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), ∀ (w : Fin (4 : ℕ)
            → CircleCoordinates), ∀ (iw : Fin (3 : ℕ)), ∀ (ew : Bool), ∀ (r2 : Fin (3 : ℕ)), ∀
            (g2 : BandPackingSymmetry), ∀ (P2 : FordFareyParameter),
        let barq : Fin 4 → CircleCoordinates :=
          ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
        ∀ (t : Fin (3 : ℕ)), (t + r2 = iw) → ((barq t.succ = w iw.succ) → ((TileCentroid T' -
            TileCentroid T = (if ew = true then (1 : ℝ) else -1) • GaussianRealPoint
            (BandVectors.1 (barq t.succ) (barq 0))) → ((p'.1 - p.1 = (if ew = true then (1 : ℝ)
            else -1) * (BandVectors.2 (barq t.succ) (barq 0)).re) → ((p'.2 - p.2 = (if ew = true
            then (1 : ℝ) else -1) * (BandVectors.2 (barq t.succ) (barq 0)).im) → (∀ (negative :
            Bool), ∀ (r : ℝ × ℝ), ∀ (r' : ℝ × ℝ), (TileCentroid (BandPackingSymmetryTileAction g2
            T') - TileCentroid (BandPackingSymmetryTileAction g2 T) = (if (ew ^^ negative) = true
            then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g2 barq ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g2 = true then -j else j) t).succ)
            (BandPackingSymmetryQuadrupleAction g2 barq (0 : Fin (4 : ℕ))))) → ((r'.1 - r.1 = (if
            (ew ^^ negative) = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g2 barq ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g2 = true then -j else j) t).succ)
            (BandPackingSymmetryQuadrupleAction g2 barq (0 : Fin (4 : ℕ)))).re : ℝ)) → ((r'.2 -
            r.2 = (if (ew ^^ negative) = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g2 barq ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g2 = true then -j else j) t).succ)
            (BandPackingSymmetryQuadrupleAction g2 barq (0 : Fin (4 : ℕ)))).im : ℝ)) → (∀ (u :
            GaussianInt), ∀ (a : GaussianInt), ∀ (u' : GaussianInt), ∀ (a' : GaussianInt), (u' -
            u = (if ew ^^ negative then 1 else -1) • BandVectors.1
            (BandPackingSymmetryQuadrupleAction g2 barq t.succ)
            (BandPackingSymmetryQuadrupleAction g2 barq 0)) → ((u' - u = (if (ew ^^ negative) =
            true then 1 else -1) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 0)) → ((BandVectors.1 (FordRecursiveQuadruple P2 (1 : Fin
            (4 : ℕ))) (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) = (⟨(↑P2.q : ℤ), (↑P2.q₁ :
            ℤ)⟩ : GaussianInt)) → ((BandVectors.1 (FordRecursiveQuadruple P2 (2 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) = (⟨-(↑P2.q : ℤ), (↑P2.q₂ : ℤ)⟩ :
            GaussianInt)) → ((BandVectors.1 (FordRecursiveQuadruple P2 (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) = (⟨(0 : ℤ), -(↑P2.q : ℤ)⟩ :
            GaussianInt)) → ((BandVectors.2 (FordRecursiveQuadruple P2 (1 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ))) = (⟨P2.p₁, P2.p⟩ : GaussianInt)) →
            ((BandVectors.2 (FordRecursiveQuadruple P2 (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple
            P2 (0 : Fin (4 : ℕ))) = (⟨P2.p₂, -P2.p⟩ : GaussianInt)) → ((BandVectors.2
            (FordRecursiveQuadruple P2 (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P2 (0 : Fin (4
            : ℕ))) = (⟨-P2.p, (0 : ℤ)⟩ : GaussianInt)) → ((r'.1 - r.1 = if ew = negative then
            -((↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 (0 :
            Fin (4 : ℕ)))).re : ℝ) + ((↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))).im : ℝ) * (0 : ℝ) - (0 : ℝ))) else
            (↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 (0 :
            Fin (4 : ℕ)))).re : ℝ) + ((↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))).im : ℝ) * (0 : ℝ) - (0 : ℝ))) → ((r'.2
            - r.2 = if ew = negative then -(↑(BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))).im : ℝ) else (↑(BandVectors.2
            (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))).im
            : ℝ)) → ((a'.re - a.re = (if (ew ^^ negative) = true then 1 else -1) * (BandVectors.2
            (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0)).re) → ((a'.im -
            a.im = (if (ew ^^ negative) = true then 1 else -1) * (BandVectors.2
            (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0)).im) → (∀ y :
            GaussianInt, FordOdometer P2 (y + BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 0)) - FordOdometer P2 y = (BandVectors.2
            (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0)).re * y.re +
            (BandVectors.2 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0)).im *
            y.im + (if t = 0 then P2.q₁ * P2.p else if t = 1 then -(P2.q * P2.p₂) else
            0))))))))))))))))))))) ) := by
  classical
  intro T T' p p' w iw ew r2 g2 P2 barq t ht hpoint hcentbar hslopebar hslopebar' negative r r'
      hcent' hsre' hsim' u a u' a' hshift hvec hv2 hv3 ha1 ha2 ha3 ha4 hsreFord hsimFord haRe haIm y
  fin_cases t
  · change FordOdometer P2 (y + BandVectors.1 (FordRecursiveQuadruple P2 1)
      (FordRecursiveQuadruple P2 0)) - FordOdometer P2 y = _
    rw [hv2]
    have identity := sub_eq_iff_eq_add.mpr ((Classical.choose_spec
        FordOdometerFamilyExistsUnique).1.2.2.2.1 P2 y)
    simp [FordOdometer, ha2] at identity ⊢
    linarith [identity]
  · change FordOdometer P2 (y + BandVectors.1 (FordRecursiveQuadruple P2 2)
      (FordRecursiveQuadruple P2 0)) - FordOdometer P2 y = _
    rw [hv3]
    have identity := sub_eq_iff_eq_add.mpr ((Classical.choose_spec
        FordOdometerFamilyExistsUnique).1.2.2.2.2.1 P2 y)
    simp [FordOdometer, ha3] at identity ⊢
    linarith [identity]
  · change FordOdometer P2 (y + BandVectors.1 (FordRecursiveQuadruple P2 3)
      (FordRecursiveQuadruple P2 0)) - FordOdometer P2 y = _
    rw [ha1]
    have identity := sub_eq_iff_eq_add.mpr ((Classical.choose_spec
        FordOdometerFamilyExistsUnique).1.2.2.1 P2 y)
    simp [FordOdometer, ha4] at identity ⊢
    linarith [identity]

private theorem hzero :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer), ∀ (g2 : BandPackingSymmetry), ∀ (P2 :
            FordFareyParameter), ∀ (k : PartialOdometer), (∀ x ∈ k.domain, k.value x =
            FordOdometer P2 x) → (∀ (u : GaussianInt), ∀ (a : GaussianInt), ∀ (b : ℤ), (∀ (x :
            GaussianInt), x ∈ (BandPackingSymmetryPartialOdometerAction g2 h).domain ↔ x - u ∈
            k.domain) → ((∀ x ∈ (BandPackingSymmetryPartialOdometerAction g2 h).domain,
            (BandPackingSymmetryPartialOdometerAction g2 h).value x = k.value (x - u) + a.re *
            x.re + a.im * x.im + b) → (∀ (u' : GaussianInt), ∀ (a' : GaussianInt), ∀ (b' : ℤ), (∀
            (x : GaussianInt), x ∈ (BandPackingSymmetryPartialOdometerAction g2 h').domain ↔ x -
            u' ∈ k.domain) → ((∀ x ∈ (BandPackingSymmetryPartialOdometerAction g2 h').domain,
            (BandPackingSymmetryPartialOdometerAction g2 h').value x = k.value (x - u') + a'.re *
            x.re + a'.im * x.im + b') → (∀ (x0 : GaussianInt), (x0 ∈
            (↑(BandPackingSymmetryPartialOdometerAction g2 h).domain : Set GaussianInt)) → ((x0 ∈
            (↑(BandPackingSymmetryPartialOdometerAction g2 h').domain : Set GaussianInt)) →
            ((BandPackingSymmetryPartialOdometerAction g2 h').value x0 -
            (BandPackingSymmetryPartialOdometerAction g2 h).value x0 = FordOdometer P2 (x0 - u')
            + a'.re * x0.re + a'.im * x0.im + b' - (FordOdometer P2 (x0 - u) + a.re * x0.re +
            a.im * x0.im + b)))))))) ) := by
  classical
  intro h h' g2 P2 k hkV u a b hud huv u' a' b' hud' huv' x0 hx0 hx0'
  rw [huv' x0 hx0', huv x0 hx0,
    hkV (x0 - u') ((hud' x0).mp hx0'),
    hkV (x0 - u) ((hud x0).mp hx0)]

private theorem hvxAt524 :
    (by
      classical
      exact
        ∀ (P2 : FordFareyParameter), ∀ (t : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (u' :
            GaussianInt), (u' - u = (1 : ℤ) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))) → (∀ (x : GaussianInt), x - u = (x -
            u') + BandVectors.1 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0))
            ) := by
  classical
  intro P2 t u u' hvec x
  calc
    x - u = x - u' + (u' - u) := by ring
    _ = _ := by rw [hvec]; ring

private theorem hvx0At530 :
    (by
      classical
      exact
        ∀ (P2 : FordFareyParameter), ∀ (t : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (u' :
            GaussianInt), (u' - u = (1 : ℤ) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))) → (∀ (x0 : GaussianInt), x0 - u = (x0
            - u') + BandVectors.1 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2
            0)) ) := by
  classical
  intro P2 t u u' hvec x0
  calc
    x0 - u = x0 - u' + (u' - u) := by ring
    _ = _ := by rw [hvec]; ring

private theorem hvxAt546 :
    (by
      classical
      exact
        ∀ (P2 : FordFareyParameter), ∀ (t : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (u' :
            GaussianInt), (u' - u = (-1 : ℤ) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))) → (∀ (x : GaussianInt), x - u' = (x -
            u) + BandVectors.1 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2 0))
            ) := by
  classical
  intro P2 t u u' hvec x
  calc
    x - u' = x - u - (u' - u) := by ring
    _ = _ := by rw [hvec]; ring

private theorem hvx0At552 :
    (by
      classical
      exact
        ∀ (P2 : FordFareyParameter), ∀ (t : Fin (3 : ℕ)), ∀ (u : GaussianInt), ∀ (u' :
            GaussianInt), (u' - u = (-1 : ℤ) • BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 (0 : Fin (4 : ℕ)))) → (∀ (x0 : GaussianInt), x0 - u' = (x0
            - u) + BandVectors.1 (FordRecursiveQuadruple P2 t.succ) (FordRecursiveQuadruple P2
            0)) ) := by
  classical
  intro P2 t u u' hvec x0
  calc
    x0 - u' = x0 - u - (u' - u) := by ring
    _ = _ := by rw [hvec]; ring

end FordBoundaryCompatibilityGeometry

theorem FordLeftBoundaryCompatibility
    (C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer)
    (hadj : LeftLatticeAdjacent C T T' h h')
    (q : Fin 4 -> CircleCoordinates) (hq : ProperBandQuadruple q)
    (hC : q 0 = C.1.1) (hline : exists i : Fin 4, (q i).1 = 0) :
    OdometerCompatibility h h' := by
-- BODY
  classical
  obtain ⟨hqT, hqT', hpdata⟩ := hadj
  obtain ⟨r0, g0, P0, hP0, hg0, hw0, hz0, heq0⟩ :=
    FordRegimeConverse q hq hline
  have hcurv := FordBoundaryCompatibilityGeometry.hcurv q r0 g0 P0 hP0 heq0
  obtain ⟨p, p', hp, hp', hcase⟩ := hpdata
  rcases hcase with hunit | hproper
  · rcases hunit with ⟨hone, orientation, v, hv, hcent, hslope, hslope'⟩
    exfalso
    have hone' : (q 0).1 = 1 := by rw [hC]; exact hone
    linarith [hcurv, hone']
  · rcases hproper with ⟨w, iw, ew, hwproper, hwchild, hwcent, hwslope, hwslope'⟩
    obtain ⟨r1, hr1, hruniq⟩ :=
      BandPredecessorNoCollision q w hq hwproper (hC.trans hwchild.symm)
    obtain ⟨iline, hiline⟩ := hline
    have wline := FordBoundaryCompatibilityGeometry.wline q w r1 hr1
        hruniq iline hiline (FordBoundaryCompatibilityGeometry.iline0 q hcurv iline hiline)
    obtain ⟨r2, g2, P2, hP2, hg2, hw2, hz2, heq2⟩ :=
      FordRegimeConverse w hwproper wline
    let barq : Fin 4 → CircleCoordinates :=
      ![w 0, w r2.succ, w (r2 + 1).succ, w (r2 + 2).succ]
    have hbar := FordBoundaryCompatibilityGeometry.hbar w hwproper r2
        g2 P2 hz2 heq2
    have hbar0 : barq 0 = q 0 := by
      simp [barq, hwchild, hC]
    have hidx : ∃ t : Fin 3, (t + r2 : Fin 3) = iw := by
      fin_cases r2 <;> fin_cases iw <;> decide
    obtain ⟨t, ht⟩ := hidx
    have hpoint := FordBoundaryCompatibilityGeometry.hpoint
        w iw r2 t ht
    have hcentbar := FordBoundaryCompatibilityGeometry.hcentbar C T T' q hC w iw ew hwchild
        hwcent r2
              hbar0 t hpoint
    have hslopebar := FordBoundaryCompatibilityGeometry.hslopebar C q hC p p' w iw ew hwchild
        hwslope r2
              hbar0 t hpoint
    have hslopebar' := FordBoundaryCompatibilityGeometry.hslopebar' C q hC p p' w iw ew hwchild
        hwslope'
              r2 hbar0 t hpoint
    obtain ⟨negative, r, r', hphase, hth, hth', hsr, hsr', hcent', hsre', hsim', hcompat⟩ :=
      LeftLatticeAdjacentPackingSymmetryTransport g2 barq hbar t ew T T' h h' p p'
        (by simpa [hbar0, hC] using hqT) (by simpa [hbar0, hC] using hqT') hp hp'
        hcentbar hslopebar hslopebar'
    apply hcompat.mp
    have heq0' := congrFun heq2 0
    have hCpos := FordBoundaryCompatibilityGeometry.hCpos w r2 g2 P2 hP2 heq0'
    obtain ⟨k, hkO, hkD, hkV⟩ := FordTileOdometerRestriction P2
    have hkO' := FordBoundaryCompatibilityGeometry.hkO' w r2 g2 P2 heq0' k hkO
    obtain ⟨u, huall, huunique⟩ :=
      TileOdometerTranslationUniqueness
        (BandPackingSymmetryQuadrupleAction g2 barq 0)
        (BandPackingSymmetryTileAction g2 T) (FordTile P2.q)
        (BandPackingSymmetryPartialOdometerAction g2 h) k hCpos hth hkO'
    obtain ⟨hu, huempty, a, b, hud, huv⟩ := huall
    obtain ⟨u', huall', huunique'⟩ :=
      TileOdometerTranslationUniqueness
        (BandPackingSymmetryQuadrupleAction g2 barq 0)
        (BandPackingSymmetryTileAction g2 T') (FordTile P2.q)
        (BandPackingSymmetryPartialOdometerAction g2 h') k hCpos hth' hkO'
    obtain ⟨hu', huempty', a', b', hud', huv'⟩ := huall'
    have hshift := FordBoundaryCompatibilityGeometry.hshift T T' w ew r2 g2 P2 hg2 t negative hcent'
                u u' (FordBoundaryCompatibilityGeometry.hcentT T g2 P2 u hu huempty)
                    (FordBoundaryCompatibilityGeometry.hcentT' T' g2 P2 u' hu' huempty')
    have hslopeH := congrArg PartialOdometerSlope (FordBoundaryCompatibilityGeometry.heqH h g2 k
        u a b hud huv)
    have hslopeH' := congrArg PartialOdometerSlope (FordBoundaryCompatibilityGeometry.heqH' h' g2
        k u' a' b' hud' huv')
    rw [hsr] at hslopeH
    rw [hsr'] at hslopeH'
    rw [PartialOdometerAffineTranslateFormulas k u a b |>.2.2.2.2.2] at hslopeH
    rw [PartialOdometerAffineTranslateFormulas k u' a' b' |>.2.2.2.2.2] at hslopeH'
    have hvec : u' - u =
        (if (ew ^^ negative) = true then 1 else -1) •
          BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 0) := FordBoundaryCompatibilityGeometry.hvec w ew r2 g2 P2
                heq2 t negative u u' hshift
    obtain ⟨_, hcfg⟩ := FordCoordinateConfiguration P2
    have hcfg := hcfg hP2
    rcases hcfg with ⟨hv1, hv2, hv3, ha1, ha2, ha3, ha4, ha5⟩
    cases hkS : PartialOdometerSlope k with
    | none => simp [hkS] at hslopeH
    | some z =>
      simp only [Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, hkS,
          Option.map_some, Option.some.injEq] at hslopeH hslopeH'
      have hsreFord := hsre'
      have hsimFord := hsim'
      have heq2bar : BandPackingSymmetryQuadrupleAction g2 barq =
          FordRecursiveQuadruple P2 := by simpa [barq] using heq2
      rw [heq2bar] at hsreFord hsimFord
      simp only [bne_iff_ne, ne_eq, ite_not, Int.reduceNeg, hg2, Bool.false_eq_true,
          ↓reduceIte, Fin.isValue, GaussianInt.intCast_re, ite_mul, neg_mul, one_mul,
          GaussianInt.intCast_im] at hsreFord hsimFord
      simp only [GaussianInt.toComplex, Zsqrtd.lift_apply_apply, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
        zero_add, mul_one] at hsreFord hsimFord
      have sr := congrArg Prod.fst hslopeH
      have sr' := congrArg Prod.fst hslopeH'
      have si := congrArg Prod.snd hslopeH
      have si' := congrArg Prod.snd hslopeH'
      dsimp at sr sr' si si'
      simp only [GaussianInt.toComplex, Zsqrtd.lift_apply_apply, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
        zero_add, mul_one] at sr sr' si si'
      have hreal (v : GaussianInt) : (GaussianInt.toComplex v).re = v.re := by
        exact (GaussianInt.intCast_re v).symm
      have himag (v : GaussianInt) : (GaussianInt.toComplex v).im = v.im := by
        exact (GaussianInt.intCast_im v).symm
      have haRe : a'.re - a.re =
          (if (ew ^^ negative) = true then 1 else -1) *
            (BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
              (FordRecursiveQuadruple P2 0)).re := FordBoundaryCompatibilityGeometry.haRe ew P2
                  t negative r r' a a' z
                  hsreFord sr sr'
      have haIm : a'.im - a.im =
          (if (ew ^^ negative) = true then 1 else -1) *
            (BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
              (FordRecursiveQuadruple P2 0)).im := FordBoundaryCompatibilityGeometry.haIm ew P2
                  t negative r r' a a' z hsimFord si si'
      have hcoc : ∀ y : GaussianInt,
          FordOdometer P2 (y + BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
            (FordRecursiveQuadruple P2 0)) - FordOdometer P2 y =
              (BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0)).re * y.re +
              (BandVectors.2 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0)).im * y.im +
              (if t = 0 then P2.q₁ * P2.p else
               if t = 1 then -(P2.q * P2.p₂) else 0) := FordBoundaryCompatibilityGeometry.hcoc T
                   T' p p' w iw ew r2 g2 P2 t ht hpoint hcentbar hslopebar hslopebar' negative r
                   r' hcent' hsre' hsim' u a u' a' hshift hvec hv2 hv3 ha1 ha2 ha3 ha4 hsreFord
                   hsimFord haRe haIm
      by_cases hdj : Disjoint
          ((BandPackingSymmetryPartialOdometerAction g2 h).domain : Set GaussianInt)
          ((BandPackingSymmetryPartialOdometerAction g2 h').domain : Set GaussianInt)
      · exact Or.inl hdj
      · right
        obtain ⟨x0, hx0, hx0'⟩ := Set.not_disjoint_iff.mp hdj
        refine ⟨(BandPackingSymmetryPartialOdometerAction g2 h').value x0 -
          (BandPackingSymmetryPartialOdometerAction g2 h).value x0, ?_⟩
        intro x hx hx'
        rw [huv' x hx', huv x hx]
        have hy := (hud x).mp hx
        have hy' := (hud' x).mp hx'
        rw [hkV (x - u) hy, hkV (x - u') hy']
        have hzero :
            (BandPackingSymmetryPartialOdometerAction g2 h').value x0 -
              (BandPackingSymmetryPartialOdometerAction g2 h).value x0 =
            FordOdometer P2 (x0 - u') + a'.re * x0.re + a'.im * x0.im + b' -
              (FordOdometer P2 (x0 - u) + a.re * x0.re + a.im * x0.im + b) :=
                  FordBoundaryCompatibilityGeometry.hzero h h' g2 P2 k hkV u a b hud huv u' a' b'
                  hud' huv' x0 hx0 hx0'
        rw [hzero]
        have hdiff := hcoc (x - u')
        have hdiff0 := hcoc (x0 - u')
        by_cases hs : (ew ^^ negative) = true
        · rw [ite_eq_left hs] at hvec haRe haIm
          have hvx : x - u = (x - u') +
              BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0) := FordBoundaryCompatibilityGeometry.hvxAt524 P2 t
                    u u' hvec x
          have hvx0 : x0 - u = (x0 - u') +
              BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0) := FordBoundaryCompatibilityGeometry.hvx0At530 P2 t
                    u u' hvec x0
          rw [← hvx] at hdiff
          rw [← hvx0] at hdiff0
          dsimp at hdiff hdiff0
          ring_nf at hdiff hdiff0 ⊢
          linear_combination -hdiff + hdiff0 +
            x.re * haRe + x.im * haIm - x0.re * haRe - x0.im * haIm
        · rw [ite_eq_right hs] at hvec haRe haIm
          ring_nf at haRe haIm
          have hdiff1 := hcoc (x - u)
          have hdiff01 := hcoc (x0 - u)
          have hvx : x - u' = (x - u) +
              BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0) := FordBoundaryCompatibilityGeometry.hvxAt546 P2 t
                    u u' hvec x
          have hvx0 : x0 - u' = (x0 - u) +
              BandVectors.1 (FordRecursiveQuadruple P2 t.succ)
                (FordRecursiveQuadruple P2 0) := FordBoundaryCompatibilityGeometry.hvx0At552 P2 t
                    u u' hvec x0
          rw [hvx, hvx0] at ⊢
          dsimp at hdiff1 hdiff01
          ring_nf at hdiff1 hdiff01 ⊢
          linear_combination hdiff1 - hdiff01 +
            (x.re - x0.re) * haRe + (x.im - x0.im) * haIm

end ApollonianSuperharmonic

end
