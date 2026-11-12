/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5570T1UnitQuadratic
public import LeanPool.ApollonianSuperharmonic.CurvatureOnePeriodicOdometer
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas

-- [TABLET NODE: P5570T1UnitNormalForm]

/-!
# P5570T1UnitNormalForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5570T1UnitNormalForm (C : BandCircle) (z : GaussianInt)
    (T : ProtoTile) (h : PartialOdometer)
    (hC : C.1.1 = (1, 1 + 2 * z)) (hh : TileOdometer C.1.1 T h) :
    ∃ (u a : GaussianInt) (b : ℤ),
      T.cells = {u} ∧
      (∀ x, x ∈ h.domain ↔ x-u ∈ (CurvatureOneOdometer z).domain) ∧
      TileCentroid T = ((u.re : ℝ)+1/2, (u.im : ℝ)+1/2) ∧
      (∀ x, x ∈ h.domain → h.value x =
        P5570T1UnitQuadratic z x + a.re*x.re + a.im*x.im + b) ∧
      PartialOdometerSlope h = some
        (((1+(z.re : ℝ))*(u.re : ℝ)+(z.im : ℝ)*(u.im : ℝ)+a.re+(z.im : ℝ)/2),
          ((z.im : ℝ)*(u.re : ℝ)-(z.re : ℝ)*(u.im : ℝ)+a.im+(z.im : ℝ)/2)) := by
-- BODY
  classical
  have hc : C.1.1.1 = 1 := by rw [hC]
  obtain ⟨u, hu⟩ := CurvatureOneBandPrototileSingleton C T hc
    (TileOdometerBandPrototile _ _ _ hh)
  let U : ProtoTile := ⟨{0}, 0⟩
  have hperiodic := CurvatureOnePeriodicOdometer C z hC
  have hcan : TileOdometer C.1.1 U (CurvatureOneOdometer z) := hperiodic.2.1
  have hbase : ∀ x, x ∈ (CurvatureOneOdometer z).domain →
      P5570T1UnitQuadratic z x = (CurvatureOneOdometer z).value x :=
    hperiodic.2.2.2.1
  have hmatrix : CircleMatrix C =
      ![![((1+z.re : ℤ) : ℝ), (z.im : ℝ)],
        ![(z.im : ℝ), (-z.re : ℝ)]] := by
    unfold CircleMatrix BandCircleEuclideanData
    simp only [hc, show C.1.1.2 = 1+2*z by rw [hC]]
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp only [
      Complex.div_re, Complex.div_im, GaussianInt.toComplex_def,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im]
    all_goals norm_num
    all_goals ring
  have translation (x v : GaussianInt) :
      P5570T1UnitQuadratic z (x+v) =
        P5570T1UnitQuadratic z x + P5570T1UnitQuadratic z v +
        ((1+z.re)*v.re+z.im*v.im)*x.re +
        (z.im*v.re-z.re*v.im)*x.im := by
    obtain ⟨w, hw, hshift⟩ := hperiodic.2.2.2.2.2.2.1 v
      (by simp [TilingLattice, hc])
    have hr : (1+z.re)*v.re+z.im*v.im = w.re := by
      have he := congrFun hw 0
      simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one] at he
      exact_mod_cast he
    have hi : z.im*v.re-z.re*v.im = w.im := by
      have he := congrFun hw 1
      simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one] at he
      have he' : z.im*v.re + -z.re*v.im = w.im := by exact_mod_cast he
      linear_combination he'
    have he : P5570T1UnitQuadratic z (x+v) =
        P5570T1UnitQuadratic z x + x.re*w.re + x.im*w.im +
          P5570T1UnitQuadratic z v := hshift x
    rw [← hr, ← hi] at he
    linear_combination he
  obtain ⟨v, ⟨hv, _, a, b, hd, hval⟩, _⟩ :=
    TileOdometerTranslationUniqueness C.1.1 T U h (CurvatureOneOdometer z)
      C.2 hh hcan
  have hvu : v = u := by
    simpa [hu, U, TileTranslation, GaussianTranslation] using hv.symm
  subst v
  have heq : h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b := by
    have hdom : h.domain =
        (PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b).domain := by
      ext x
      rw [(PartialOdometerAffineTranslateFormulas _ u a b).2.1]
      exact hd x
    have hvalues : h.value =
        (PartialOdometerAffineTranslate (CurvatureOneOdometer z) u a b).value := by
      funext x
      by_cases hx : x ∈ h.domain
      · rw [hval x hx, (PartialOdometerAffineTranslateFormulas _ u a b).2.2.1 x
          (by rwa [← hdom])]
      · rw [h.value_outside x hx,
          (PartialOdometerAffineTranslate _ u a b).value_outside x (by rwa [← hdom])]
    cases h
    congr
  have hsquares : PartialOdometerSquares (CurvatureOneOdometer z) = {0} := by
    change PartialOdometerSquares (CurvatureOneOdometer 0) = {0}
    decide +kernel
  have hslope : PartialOdometerSlope (CurvatureOneOdometer z) =
      some ((z.im : ℝ)/2, (z.im : ℝ)/2) := by
    unfold PartialOdometerSlope
    rw [hsquares]
    simp [CurvatureOneOdometer, Zsqrtd.ext_iff]
  let A : GaussianInt := ⟨a.re-((1+z.re)*u.re+z.im*u.im),
    a.im-(z.im*u.re-z.re*u.im)⟩
  refine ⟨u, A, b+P5570T1UnitQuadratic z (-u), hu, hd, ?_, ?_, ?_⟩
  · simp [TileCentroid, hu]
  · intro x hx
    rw [hval x hx, ← hbase (x-u) ((hd x).mp hx)]
    have ht := translation x (-u)
    simp only [← sub_eq_add_neg] at ht
    rw [ht]
    simp [A]
    ring
  · rw [heq, (PartialOdometerAffineTranslateFormulas _ u a b).2.2.2.2.2, hslope]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    dsimp [A]
    push_cast
    constructor <;> ring

end ApollonianSuperharmonic

end
