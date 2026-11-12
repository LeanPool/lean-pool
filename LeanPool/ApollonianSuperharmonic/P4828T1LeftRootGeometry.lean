/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.RootComplexCoordinates

public import LeanPool.ApollonianSuperharmonic.P4828T1Root
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import Mathlib.Analysis.Convex.Combination
public import LeanPool.ApollonianSuperharmonic.P4828T1Disk

-- [TABLET NODE: P4828T1LeftRootGeometry]

/-!
# P4828T1LeftRootGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RootGeometryLeft

private noncomputable def q (a : GaussianInt) := P4828T1Root a false

private noncomputable def L (a : GaussianInt) : Real := 2 * (a.re : Real)

private noncomputable def y (a : GaussianInt) : Real := 2 * (a.im : Real)

private noncomputable def vertices (a : GaussianInt) : Set Complex := {p | ∃ j : Fin 3, 0 < ((q
    a) j.succ).1 ∧
    (p = ((q a) j.succ).2 / (((q a) j.succ).1 : Real) ∨ ∃ k : Fin 3,
      ((q a) k.succ).1 = 0 ∧ p = ⟨if ((q a) k.succ).2 = -1 then (L a) else (L a) + 2,
        ((((q a) j.succ).2 : Complex) / (((q a) j.succ).1 : Real)).im⟩)}

private noncomputable def bl (a : GaussianInt) : Complex := ⟨(L a), (y a)⟩

private noncomputable def br (a : GaussianInt) : Complex := ⟨(L a) + 1, (y a)⟩

private noncomputable def tl (a : GaussianInt) : Complex := ⟨(L a), (y a) + 2⟩

private noncomputable def tr (a : GaussianInt) : Complex := ⟨(L a) + 1, (y a) + 2⟩

private abbrev hU0 := RootComplexCoordinates.lowerGaussianCoordinate

private abbrev hU1 := RootComplexCoordinates.upperGaussianCoordinate

private abbrev hU0c := RootComplexCoordinates.lowerComplexCoordinate

private abbrev hU1c := RootComplexCoordinates.upperComplexCoordinate

private abbrev htwo_re := RootComplexCoordinates.twoReal

private abbrev htwo_im := RootComplexCoordinates.twoImaginary

private theorem hvertices (a : GaussianInt) : (vertices a) = {(bl a), (br a), (tl a), (tr a)} := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  let bl : Complex := ⟨L, y⟩
  let br : Complex := ⟨L + 1, y⟩
  let tl : Complex := ⟨L, y + 2⟩
  let tr : Complex := ⟨L + 1, y + 2⟩
  have hU0 : ((1 + 2 * a : GaussianInt) : Complex) = ⟨L + 1, y⟩ := hU0 a
  have hU1 : ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) =
      ⟨L + 1, y + 2⟩ := hU1 a
  have hU0c : (1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) = ⟨L + 1, y⟩ := hU0c a
  have hU1c : (1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (⟨0, 1⟩ : GaussianInt) = ⟨L + 1, y + 2⟩ := hU1c a
  have htwo_re : (GaussianInt.toComplex (2 : GaussianInt)).re = 2 := htwo_re
  have htwo_im : (GaussianInt.toComplex (2 : GaussianInt)).im = 0 := htwo_im
  change (vertices = {bl, br, tl, tr})
  ext p
  constructor
  · rintro ⟨j, hj, hp⟩
    fin_cases j
    · simp only [P4828T1Root, Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, Fin.zero_eta,
        Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        zero_lt_one, map_add, map_one, map_mul, Int.cast_one, Complex.ofReal_one, div_one,
        Matrix.cons_val_succ, Complex.add_im, Complex.one_im, Complex.mul_im, zero_add, q]
        at hj hp
      rcases hp with hp | ⟨k, hk, hp⟩
      · subst p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        right; left
        simpa [br] using hU0c
      · fin_cases k
        · simp [] at hk
        · simp [] at hk
          subst p
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          left
          apply Complex.ext <;> simp [bl, L, y, htwo_re, htwo_im,
            ]
        · simp [] at hk
    · simp [q, P4828T1Root] at hj
    · simp only [P4828T1Root, Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, Fin.reduceFinMk,
        Fin.reduceSucc, Matrix.cons_val, zero_lt_one, map_add, map_one, map_mul, Int.cast_one,
        Complex.ofReal_one, div_one, Matrix.cons_val_succ, Complex.add_im, Complex.one_im,
        Complex.mul_im, zero_add, GaussianInt.im_toComplex, mul_one, GaussianInt.re_toComplex,
        Int.cast_zero, mul_zero, add_zero, q] at hj hp
      rcases hp with hp | ⟨k, hk, hp⟩
      · subst p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right
        simpa [tr] using hU1c
      · fin_cases k
        · simp [] at hk
        · simp [] at hk
          subst p
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          right; right; left
          apply Complex.ext <;> simp [tl, L, y, htwo_re, htwo_im,
            ]
        · simp [] at hk
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp | hp
    · subst p
      exact ⟨⟨0, by omega⟩,
        by change 0 < (P4828T1Root a false ⟨1, by omega⟩).1; change 0 < 1; norm_num,
        Or.inr ⟨⟨1, by omega⟩,
          by change (P4828T1Root a false ⟨2, by omega⟩).1 = 0; change (0 : ℤ) = 0; rfl,
          by apply Complex.ext <;> simp [bl, q, P4828T1Root, L, y, htwo_re, htwo_im,
            ] ⟩⟩
    · subst p
      exact ⟨⟨0, by omega⟩,
        by change 0 < (P4828T1Root a false ⟨1, by omega⟩).1; change 0 < 1; norm_num,
        Or.inl (by simpa [q, P4828T1Root] using hU0.symm)⟩
    · subst p
      exact ⟨⟨2, by omega⟩,
        by change 0 < (P4828T1Root a false ⟨3, by omega⟩).1; change 0 < 1; norm_num,
        Or.inr ⟨⟨1, by omega⟩,
          by change (P4828T1Root a false ⟨2, by omega⟩).1 = 0; change (0 : ℤ) = 0; rfl,
          by apply Complex.ext <;> simp [tl, q, P4828T1Root, L, y, htwo_re, htwo_im,
            ] ⟩⟩
    · subst p
      exact ⟨⟨2, by omega⟩,
        by change 0 < (P4828T1Root a false ⟨3, by omega⟩).1; change 0 < 1; norm_num,
        Or.inl (by simpa [q, P4828T1Root] using hU1.symm)⟩

private theorem himage (a : GaussianInt) : Complex.equivRealProdLm '' (vertices a) =
      ({(L a), (L a) + 1} : Set Real) ×ˢ {(y a), (y a) + 2} := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  let bl : Complex := ⟨L, y⟩
  let br : Complex := ⟨L + 1, y⟩
  let tl : Complex := ⟨L, y + 2⟩
  let tr : Complex := ⟨L + 1, y + 2⟩
  have hvertices : vertices = {bl, br, tl, tr} := hvertices a
  change (Complex.equivRealProdLm '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2})
  rw [hvertices]
  ext z
  simp [bl, br, tl, tr, Complex.equivRealProdLm]; aesop

private theorem hcornerHull (a : GaussianInt) : convexHull Real
      (({(L a), (L a) + 1} : Set Real) ×ˢ ({(y a), (y a) + 2} : Set Real)) =
      Set.Icc (L a) ((L a) + 1) ×ˢ Set.Icc (y a) ((y a) + 2) := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  change (convexHull Real
      (({L, L + 1} : Set Real) ×ˢ ({y, y + 2} : Set Real)) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2))
  rw [convexHull_prod, convexHull_pair, convexHull_pair,
    segment_eq_Icc (by linarith), segment_eq_Icc (by linarith)]

private theorem hrectImage (a : GaussianInt) : Complex.equivRealProdLm ''
      ((Set.Icc (L a) ((L a) + 1)) ×ℂ (Set.Icc (y a) ((y a) + 2))) =
      Set.Icc (L a) ((L a) + 1) ×ˢ Set.Icc (y a) ((y a) + 2) := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  change (Complex.equivRealProdLm ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2))
  ext z
  simp only [Set.mem_image, Set.mem_prod, Complex.mem_reProdIm]
  constructor
  · rintro ⟨p, ⟨hp, hp'⟩, rfl⟩
    exact ⟨hp, hp'⟩
  · rintro ⟨hz, hz'⟩
    refine ⟨Complex.equivRealProdLm.symm z, ?_, Complex.equivRealProdLm.apply_symm_apply z⟩
    constructor
    · simpa [Complex.equivRealProdLm_symm_apply] using hz
    · simpa [Complex.equivRealProdLm_symm_apply] using hz'

private theorem himageLin (a : GaussianInt) : Complex.equivRealProdLm.toLinearMap '' (vertices a) =
      ({(L a), (L a) + 1} : Set Real) ×ˢ {(y a), (y a) + 2} := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  have himage : Complex.equivRealProdLm '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2} := himage a
  change (Complex.equivRealProdLm.toLinearMap '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2})
  change Complex.equivRealProdLm '' vertices = _
  exact himage

private theorem hrectImageLin (a : GaussianInt) : Complex.equivRealProdLm.toLinearMap ''
      ((Set.Icc (L a) ((L a) + 1)) ×ℂ (Set.Icc (y a) ((y a) + 2))) =
      Set.Icc (L a) ((L a) + 1) ×ˢ Set.Icc (y a) ((y a) + 2) := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  have hrectImage : Complex.equivRealProdLm ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := hrectImage a
  change (Complex.equivRealProdLm.toLinearMap ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2))
  change Complex.equivRealProdLm ''
    ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) = _
  exact hrectImage

private theorem hHull (a : GaussianInt) : convexHull Real (vertices a) =
      (Set.Icc (L a) ((L a) + 1)) ×ℂ (Set.Icc (y a) ((y a) + 2)) := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  have hcornerHull : convexHull Real
      (({L, L + 1} : Set Real) ×ˢ ({y, y + 2} : Set Real)) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := hcornerHull a
  have himageLin : Complex.equivRealProdLm.toLinearMap '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2} := himageLin a
  have hrectImageLin : Complex.equivRealProdLm.toLinearMap ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := hrectImageLin a
  change (convexHull Real vertices =
      (Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2)))
  apply (Set.image_injective.mpr Complex.equivRealProdLm.injective)
  have hlin := LinearMap.image_convexHull
    Complex.equivRealProdLm.toLinearMap vertices
  change Complex.equivRealProdLm.toLinearMap ''
    (convexHull Real vertices) = Complex.equivRealProdLm.toLinearMap ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2)))
  rw [hlin, himageLin, hcornerHull, hrectImageLin]

private abbrev rectangleInterior := RootComplexCoordinates.rectangleInterior

private theorem hInterior (a : GaussianInt) : interior (convexHull Real (vertices a)) =
      {p : Complex | (L a) < p.re ∧ p.re < (L a) + 1 ∧ (y a) < p.im ∧ p.im < (y a) + 2} := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  have hHull : convexHull Real vertices =
      (Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2)) := hHull a
  have rectangleInterior (l u v w : Real) :
      interior (Set.Icc l u ×ℂ Set.Icc v w) =
        {z : Complex | l < z.re ∧ z.re < u ∧ v < z.im ∧ z.im < w} := rectangleInterior l u v w
  change (interior (convexHull Real vertices) =
      {p : Complex | L < p.re ∧ p.re < L + 1 ∧ y < p.im ∧ p.im < y + 2})
  rw [hHull]
  exact rectangleInterior L (L + 1) y (y + 2)

private theorem hcenter0 (a : GaussianInt) :
      (((q a) (0 : Fin 3).succ).2 : Complex) / (((q a) (0 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a : GaussianInt) : Complex) := by
  classical
  let q := P4828T1Root a false
  change (((q (0 : Fin 3).succ).2 : Complex) / ((q (0 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a : GaussianInt) : Complex))
  simp [q, P4828T1Root]

private theorem hcenter1 (a : GaussianInt) :
      (((q a) (2 : Fin 3).succ).2 : Complex) / (((q a) (2 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) := by
  classical
  let q := P4828T1Root a false
  change (((q (2 : Fin 3).succ).2 : Complex) / ((q (2 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex))
  simp [q, P4828T1Root]

private theorem hGap (a : GaussianInt) : P4828T1Gap (L a) (q a) = {p : Complex |
      (L a) < p.re ∧ p.re < (L a) + 1 ∧ (y a) < p.im ∧ p.im < (y a) + 2 ∧
      1 < dist p ((1 + 2 * a : GaussianInt) : Complex) ∧
      1 < dist p ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)} := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  have hInterior : interior (convexHull Real vertices) =
      {p : Complex | L < p.re ∧ p.re < L + 1 ∧ y < p.im ∧ p.im < y + 2} := hInterior a
  have hcenter0 :
      ((q (0 : Fin 3).succ).2 : Complex) / ((q (0 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a : GaussianInt) : Complex) := hcenter0 a
  have hcenter1 :
      ((q (2 : Fin 3).succ).2 : Complex) / ((q (2 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) := hcenter1 a
  change (P4828T1Gap L q = {p : Complex |
      L < p.re ∧ p.re < L + 1 ∧ y < p.im ∧ p.im < y + 2 ∧
      1 < dist p ((1 + 2 * a : GaussianInt) : Complex) ∧
      1 < dist p ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)})
  ext p
  change (p ∈ interior (convexHull Real vertices) ∧
    ∀ j : Fin 3, 0 < (q j.succ).1 →
      (1 / ((q j.succ).1 : Real)) <
        dist p (((q j.succ).2 : Complex) / ((q j.succ).1 : Real))) ↔ _
  rw [hInterior]
  constructor
  · rintro ⟨⟨hxl, hxr, hyl, hyr⟩, hdist⟩
    have hd0 := hdist 0 (by simp [q, P4828T1Root])
    have hd1 := hdist 2 (by simp [q, P4828T1Root])
    refine ⟨hxl, hxr, hyl, hyr, ?_, ?_⟩
    · simpa [q, P4828T1Root, hcenter0] using hd0
    · simpa [q, P4828T1Root, hcenter1] using hd1
  · rintro ⟨hxl, hxr, hyl, hyr, hd0, hd1⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hxl, hxr, hyl, hyr⟩
    · intro j hj
      fin_cases j
      · simpa [q, P4828T1Root, hcenter0] using hd0
      · simp [q, P4828T1Root] at hj
      · simpa [q, P4828T1Root, hcenter1] using hd1

private noncomputable def child (a : GaussianInt) : Complex := ⟨(L a) + 1 / 4, (y a) + 1⟩

private theorem hchild (a : GaussianInt) :
      (((q a) (0 : Fin 4)).2 : Complex) / (((q a) (0 : Fin 4)).1 : Real) = (child a) := by
  classical
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let child : Complex := ⟨L + 1 / 4, y + 1⟩
  change (((q (0 : Fin 4)).2 : Complex) / ((q (0 : Fin 4)).1 : Real) = child)
  change ((1 + 8 * a + 4 * ⟨0, 1⟩ : GaussianInt) : Complex) / 4 = _
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext
  · simp [child, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
      L]; field_simp; ring
  · simp [child, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
      y]; field_simp; ring

private abbrev hs25 := RootComplexCoordinates.sqrtTwentyFive

private abbrev hs16 := RootComplexCoordinates.sqrtSixteen

private theorem hdist0 (a : GaussianInt) : dist (child a) (br a) = (5 : Real) / 4 := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let br : Complex := ⟨L + 1, y⟩
  let child : Complex := ⟨L + 1 / 4, y + 1⟩
  have hs25 : Real.sqrt (25 : Real) = 5 := hs25
  have hs16 : Real.sqrt (16 : Real) = 4 := hs16
  change (dist child br = (5 : Real) / 4)
  norm_num [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply,
    hs25, hs16, child, br]

private theorem hdist1 (a : GaussianInt) : dist (child a) (tr a) = (5 : Real) / 4 := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  let tr : Complex := ⟨L + 1, y + 2⟩
  let child : Complex := ⟨L + 1 / 4, y + 1⟩
  have hs25 : Real.sqrt (25 : Real) = 5 := hs25
  have hs16 : Real.sqrt (16 : Real) = 4 := hs16
  change (dist child tr = (5 : Real) / 4)
  norm_num [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply,
    hs25, hs16, child, tr]

end RootGeometryLeft

theorem P4828T1LeftRootGeometry (a : GaussianInt) :
    let q := P4828T1Root a false
    let L : Real := 2 * (a.re : Real)
    ProperBandQuadruple q ∧ P4828T1LineSupport L q ∧
      P4828T1Disk (q 0) ⊆ P4828T1Gap L q ∧
      P4828T1Gap L q = {p : Complex |
        L < p.re ∧ p.re < L + 1 ∧
        2 * (a.im : Real) < p.im ∧ p.im < 2 * (a.im : Real) + 2 ∧
        1 < dist p ((1 + 2 * a : GaussianInt) : Complex) ∧
        1 < dist p ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)} := by
-- BODY
  dsimp only
  let q := P4828T1Root a false
  let L : Real := 2 * (a.re : Real)
  constructor
  · constructor
    · convert (SemiProperQuadruple.successor
          (SemiProperQuadruple.rotate (SemiProperQuadruple.base a))) using 1;
            simp [P4828T1Root]; ring
    · intro j
      fin_cases j <;> simp [P4828T1Root]
  constructor
  · refine ⟨?_, ?_⟩
    · intro k hk
      fin_cases k <;> simp [P4828T1Root] at hk ⊢
    · intro k j hk hj
      fin_cases k <;> fin_cases j <;>
        simp [P4828T1Root] at hk hj ⊢; ring
  let y : Real := 2 * (a.im : Real)
  let vertices : Set Complex := {p | ∃ j : Fin 3, 0 < (q j.succ).1 ∧
    (p = (q j.succ).2 / ((q j.succ).1 : Real) ∨ ∃ k : Fin 3,
      (q k.succ).1 = 0 ∧ p = ⟨if (q k.succ).2 = -1 then L else L + 2,
        (((q j.succ).2 : Complex) / ((q j.succ).1 : Real)).im⟩)}
  let bl : Complex := ⟨L, y⟩
  let br : Complex := ⟨L + 1, y⟩
  let tl : Complex := ⟨L, y + 2⟩
  let tr : Complex := ⟨L + 1, y + 2⟩
  have hU0 : ((1 + 2 * a : GaussianInt) : Complex) = ⟨L + 1, y⟩ :=
      RootComplexCoordinates.lowerGaussianCoordinate a
  have hU1 : ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) =
      ⟨L + 1, y + 2⟩ := RootComplexCoordinates.upperGaussianCoordinate a
  have hU0c : (1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) = ⟨L + 1, y⟩ := RootComplexCoordinates.lowerComplexCoordinate a
  have hU1c : (1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (⟨0, 1⟩ : GaussianInt) = ⟨L + 1, y + 2⟩ := RootComplexCoordinates.upperComplexCoordinate a
  have htwo_re : (GaussianInt.toComplex (2 : GaussianInt)).re = 2 := RootComplexCoordinates.twoReal
  have htwo_im : (GaussianInt.toComplex (2 : GaussianInt)).im = 0 :=
      RootComplexCoordinates.twoImaginary
  have hvertices : vertices = {bl, br, tl, tr} := RootGeometryLeft.hvertices a
  have himage : Complex.equivRealProdLm '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2} := RootGeometryLeft.himage a
  have hcornerHull : convexHull Real
      (({L, L + 1} : Set Real) ×ˢ ({y, y + 2} : Set Real)) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := RootGeometryLeft.hcornerHull a
  have hrectImage : Complex.equivRealProdLm ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := RootGeometryLeft.hrectImage a
  have himageLin : Complex.equivRealProdLm.toLinearMap '' vertices =
      ({L, L + 1} : Set Real) ×ˢ {y, y + 2} := RootGeometryLeft.himageLin a
  have hrectImageLin : Complex.equivRealProdLm.toLinearMap ''
      ((Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2))) =
      Set.Icc L (L + 1) ×ˢ Set.Icc y (y + 2) := RootGeometryLeft.hrectImageLin a
  have hHull : convexHull Real vertices =
      (Set.Icc L (L + 1)) ×ℂ (Set.Icc y (y + 2)) := RootGeometryLeft.hHull a
  have rectangleInterior (l u v w : Real) :
      interior (Set.Icc l u ×ℂ Set.Icc v w) =
        {z : Complex | l < z.re ∧ z.re < u ∧ v < z.im ∧ z.im < w} :=
            RootComplexCoordinates.rectangleInterior l u v w
  have hInterior : interior (convexHull Real vertices) =
      {p : Complex | L < p.re ∧ p.re < L + 1 ∧ y < p.im ∧ p.im < y + 2} :=
          RootGeometryLeft.hInterior a
  have hcenter0 :
      ((q (0 : Fin 3).succ).2 : Complex) / ((q (0 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a : GaussianInt) : Complex) := RootGeometryLeft.hcenter0 a
  have hcenter1 :
      ((q (2 : Fin 3).succ).2 : Complex) / ((q (2 : Fin 3).succ).1 : Real) =
        ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) := RootGeometryLeft.hcenter1 a
  have hGap : P4828T1Gap L q = {p : Complex |
      L < p.re ∧ p.re < L + 1 ∧ y < p.im ∧ p.im < y + 2 ∧
      1 < dist p ((1 + 2 * a : GaussianInt) : Complex) ∧
      1 < dist p ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)} := RootGeometryLeft.hGap a
  let child : Complex := ⟨L + 1 / 4, y + 1⟩
  have hchild :
      ((q (0 : Fin 4)).2 : Complex) / ((q (0 : Fin 4)).1 : Real) = child :=
          RootGeometryLeft.hchild a
  have hs25 : Real.sqrt (25 : Real) = 5 := RootComplexCoordinates.sqrtTwentyFive
  have hs16 : Real.sqrt (16 : Real) = 4 := RootComplexCoordinates.sqrtSixteen
  have hdist0 : dist child br = (5 : Real) / 4 := RootGeometryLeft.hdist0 a
  have hdist1 : dist child tr = (5 : Real) / 4 := RootGeometryLeft.hdist1 a
  · constructor
    · rw [hGap]
      intro p hp
      have hballMember : dist p
          (((q (0 : Fin 4)).2 : Complex) / ((q (0 : Fin 4)).1 : Real)) <
            1 / ((q (0 : Fin 4)).1 : Real) := by
        simpa [P4828T1Disk] using hp
      rw [hchild] at hballMember
      have hcurv0 : (q (0 : Fin 4)).1 = 4 := by
        change (P4828T1Root a false ⟨0, by omega⟩).1 = 4
        norm_num [P4828T1Root]
      rw [hcurv0] at hballMember
      have hpball : dist p child < (1 : Real) / 4 := by
        simpa using hballMember
      have hnorm : ‖p - child‖ < (1 : Real) / 4 := by
        simpa [Complex.dist_eq] using hpball
      have hre : |p.re - (L + 1 / 4)| < (1 : Real) / 4 := by
        have h := lt_of_le_of_lt (Complex.abs_re_le_norm (p - child)) hnorm
        simpa [child, Complex.sub_re] using h
      have him : |p.im - (y + 1)| < (1 : Real) / 4 := by
        have h := lt_of_le_of_lt (Complex.abs_im_le_norm (p - child)) hnorm
        simpa [child, Complex.sub_im] using h
      have hre' := abs_lt.mp hre
      have him' := abs_lt.mp him
      have htri0 := dist_triangle child p br
      have htri1 := dist_triangle child p tr
      rw [dist_comm child p] at htri0 htri1
      have hparent0 : 1 < dist p br := by linarith
      have hparent1 : 1 < dist p tr := by linarith
      refine ⟨by linarith [hre'.1], by linarith [hre'.2],
        by linarith [him'.1], by linarith [him'.2], ?_, ?_⟩
      · simpa [br, hU0] using hparent0
      · simpa [tr, hU1] using hparent1
    · simpa [y, L, q, P4828T1Root] using hGap

end ApollonianSuperharmonic

end
