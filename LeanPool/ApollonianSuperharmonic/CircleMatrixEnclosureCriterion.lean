/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5630T1SymmetricMatrixPositivityCriterion
public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.SymmetricMatrixCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.SymmetricMatrixCoordinates
public import Mathlib.Analysis.Complex.Basic

-- [TABLET NODE: CircleMatrixEnclosureCriterion]

/-!
# CircleMatrixEnclosureCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CircleMatrixEnclosureCriterion
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (C : BandCircle) :
    (((CircleMatrix C - A).PosSemidef) ↔
      dist (SymmetricMatrixCoordinates A).1
          (BandCircleEuclideanData C).center +
        (SymmetricMatrixCoordinates A).2 ≤
          (BandCircleEuclideanData C).radius) ∧
    (((A - CircleMatrix C).PosDef) ↔
      dist (SymmetricMatrixCoordinates A).1
          (BandCircleEuclideanData C).center +
        (BandCircleEuclideanData C).radius <
          (SymmetricMatrixCoordinates A).2) := by
-- BODY
  have hCircleCoordinates :
      (CircleMatrix C).IsSymm ∧
        SymmetricMatrixCoordinates (CircleMatrix C) =
          ((BandCircleEuclideanData C).center,
            (BandCircleEuclideanData C).radius) := by
    have hc : (C.1.1.1 : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt C.2)
    constructor
    · apply Matrix.IsSymm.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [CircleMatrix]
    · apply Prod.ext
      · apply Complex.ext <;>
          simp [SymmetricMatrixCoordinates, CircleMatrix,
            BandCircleEuclideanData]; field_simp; ring
      · change Matrix.trace (CircleMatrix C) = 1 / (C.1.1.1 : Real)
        rw [Matrix.trace_fin_two]
        simp [CircleMatrix, BandCircleEuclideanData]
        field_simp
        ring
  have pscale (N : Matrix (Fin 2) (Fin 2) Real) :
      (((2 : Real)⁻¹) • N).PosSemidef ↔ N.PosSemidef := by
    constructor
    · intro h
      rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h ⊢
      refine ⟨?_, ?_⟩
      · simpa [Matrix.smul_apply] using h.1
      · intro z
        have hz := h.2 z
        simp [Matrix.mulVec, Matrix.smul_apply, dotProduct] at hz ⊢
        nlinarith [hz]
    · intro h
      rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h ⊢
      refine ⟨?_, ?_⟩
      · simpa [Matrix.smul_apply] using h.1
      · intro z
        have hz := h.2 z
        simp [Matrix.mulVec, Matrix.smul_apply, dotProduct] at hz ⊢
        nlinarith [hz]
  have dscale (N : Matrix (Fin 2) (Fin 2) Real) :
      (((2 : Real)⁻¹) • N).PosDef ↔ N.PosDef := by
    constructor
    · intro h
      rw [Matrix.posDef_iff_dotProduct_mulVec] at h ⊢
      refine ⟨?_, ?_⟩
      · simpa [Matrix.smul_apply] using h.1
      · intro z hz
        have hz' := h.2 hz
        simp [Matrix.mulVec, Matrix.smul_apply, dotProduct] at hz' ⊢
        nlinarith [hz']
    · intro h
      rw [Matrix.posDef_iff_dotProduct_mulVec] at h ⊢
      refine ⟨?_, ?_⟩
      · simpa [Matrix.smul_apply] using h.1
      · intro z hz
        have hz' := h.2 hz
        simp [Matrix.mulVec, Matrix.smul_apply, dotProduct] at hz' ⊢
        nlinarith [hz']
  have circleIdentity :
      CircleMatrix C = (2 : Real)⁻¹ •
        ((![![((BandCircleEuclideanData C).radius +
            (BandCircleEuclideanData C).center.re),
            (BandCircleEuclideanData C).center.im],
        ![(BandCircleEuclideanData C).center.im,
            (BandCircleEuclideanData C).radius -
              (BandCircleEuclideanData C).center.re]]) :
          Matrix (Fin 2) (Fin 2) Real) := by
    simpa [hCircleCoordinates.2] using
      (SymmetricMatrixCoordinateIdentity (CircleMatrix C)
        hCircleCoordinates.1)
  let x := SymmetricMatrixCoordinates A
  let e := BandCircleEuclideanData C
  have entrySub (P Q : Matrix (Fin 2) (Fin 2) Real) (i j : Fin 2) :
      (P - Q) i j = P i j - Q i j := by rfl
  have entrySmul (a : Real) (P : Matrix (Fin 2) (Fin 2) Real) (i j : Fin 2) :
      (a • P) i j = a * P i j := by rfl
  have hminus :
      CircleMatrix C - A = (2 : Real)⁻¹ •
        ((![![e.radius - x.2 + (e.center - x.1).re,
            (e.center - x.1).im],
        ![(e.center - x.1).im,
            e.radius - x.2 - (e.center - x.1).re]]) : Matrix (Fin 2) (Fin 2) Real) := by
    rw [circleIdentity, SymmetricMatrixCoordinateIdentity A hA]
    dsimp [x, e]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals change ((2 : Real)⁻¹ * _ - (2 : Real)⁻¹ * _) = (2 : Real)⁻¹ * _
    all_goals norm_num [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]; ring_nf
  have hplus :
      A - CircleMatrix C = (2 : Real)⁻¹ •
        ((![![x.2 - e.radius + (x.1 - e.center).re,
            (x.1 - e.center).im],
        ![(x.1 - e.center).im,
            x.2 - e.radius - (x.1 - e.center).re]]) : Matrix (Fin 2) (Fin 2) Real) := by
    rw [SymmetricMatrixCoordinateIdentity A hA, circleIdentity]
    dsimp [x, e]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals change ((2 : Real)⁻¹ * _ - (2 : Real)⁻¹ * _) = (2 : Real)⁻¹ * _
    all_goals norm_num [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]; ring_nf
  have hnorm :
      Real.sqrt (((e.center - x.1).re) ^ 2 + ((e.center - x.1).im) ^ 2) =
        dist x.1 e.center := by
    rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    congr 1; ring_nf
  have hcrit := P5630T1SymmetricMatrixPositivityCriterion
    (e.radius - x.2) (e.center - x.1).re (e.center - x.1).im
  have hcrit' := P5630T1SymmetricMatrixPositivityCriterion
    (x.2 - e.radius) (x.1 - e.center).re (x.1 - e.center).im
  let Nminus : Matrix (Fin 2) (Fin 2) Real :=
    ![![e.radius - x.2 + (e.center - x.1).re, (e.center - x.1).im],
      ![(e.center - x.1).im, e.radius - x.2 - (e.center - x.1).re]]
  let Nplus : Matrix (Fin 2) (Fin 2) Real :=
    ![![x.2 - e.radius + (x.1 - e.center).re, (x.1 - e.center).im],
      ![(x.1 - e.center).im, x.2 - e.radius - (x.1 - e.center).re]]
  have hcminus : Nminus.PosSemidef ↔
      Real.sqrt (((e.center - x.1).re) ^ 2 + ((e.center - x.1).im) ^ 2) ≤
        e.radius - x.2 := by
    simpa [Nminus] using hcrit.1
  have hcplus : Nplus.PosDef ↔
      Real.sqrt (((x.1 - e.center).re) ^ 2 + ((x.1 - e.center).im) ^ 2) <
        x.2 - e.radius := by
    simpa [Nplus] using hcrit'.2
  constructor
  · rw [hminus]
    change (((2 : Real)⁻¹) • Nminus).PosSemidef ↔ _
    rw [pscale Nminus]
    rw [← hnorm]
    constructor <;> intro hh
    · have ht := hcminus.mp hh
      linarith
    · apply hcminus.mpr
      linarith
  · rw [hplus]
    change (((2 : Real)⁻¹) • Nplus).PosDef ↔ _
    rw [dscale Nplus]
    have hnorm' :
        Real.sqrt (((x.1 - e.center).re) ^ 2 + ((x.1 - e.center).im) ^ 2) =
          dist x.1 e.center := by
      rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
      congr 1; ring_nf
    rw [← hnorm']
    constructor <;> intro hh
    · have ht := hcplus.mp hh
      linarith
    · apply hcplus.mpr
      linarith

end ApollonianSuperharmonic

end
