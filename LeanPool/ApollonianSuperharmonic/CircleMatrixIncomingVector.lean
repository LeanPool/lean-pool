/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing
public import LeanPool.ApollonianSuperharmonic.CircleMatrix

-- [TABLET NODE: CircleMatrixIncomingVector]

/-!
# CircleMatrixIncomingVector

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CircleMatrixIncomingVector (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : SemiProperQuadruple q)
    (hchild : q 0 = C.1.1) (j : Fin 3) :
    Matrix.mulVec (CircleMatrix C)
        ![((BandVectors.1 (q j.succ) (q 0)).re : ℝ),
          ((BandVectors.1 (q j.succ) (q 0)).im : ℝ)] =
      ![((BandVectors.2 (q j.succ) (q 0)).re : ℝ),
        ((BandVectors.2 (q j.succ) (q 0)).im : ℝ)] := by
-- BODY
  have hmatrix :
      CircleMatrix C =
        let c : ℝ := C.1.1.1
        let x : ℝ := C.1.1.2.re
        let y : ℝ := C.1.1.2.im
        (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  have hidx : j.succ ≠ (0 : Fin 4) := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  have hpos : 0 < (q 0).1 := by
    rw [hchild]
    exact C.2
  have hv : BandVectors.1 (q j.succ) (q 0) ≠ 0 :=
    VectorNonvanishing q hq j.succ 0 hidx (Or.inr hpos)
  have hident := VectorSquareProduct q hq j.succ 0 hidx
  have htan := TangencyCoordinateIdentity q hq j.succ 0 hidx
  have hnorm : Zsqrtd.norm (BandVectors.1 (q j.succ) (q 0)) =
      (q j.succ).1 + (q 0).1 := by
    have hs : Zsqrtd.norm (BandVectors.1 (q j.succ) (q 0)) ^ 2 =
        ((q j.succ).1 + (q 0).1) ^ 2 := by
      calc
        Zsqrtd.norm (BandVectors.1 (q j.succ) (q 0)) ^ 2 =
            Zsqrtd.norm (BandVectors.1 (q j.succ) (q 0) ^ 2) := by
              simp [pow_two]
        _ = Zsqrtd.norm ((q 0).1 • (q j.succ).2 -
            (q j.succ).1 • (q 0).2) := by rw [hident.1]
        _ = ((q j.succ).1 + (q 0).1) ^ 2 := htan
    have hn := GaussianInt.norm_nonneg (BandVectors.1 (q j.succ) (q 0))
    have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
        SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 := by
      intro r hr
      induction hr with
      | base z =>
          intro k
          fin_cases k <;> simp
      | rotate hr ih =>
          intro k
          fin_cases k
          · simpa using ih 0
          · simpa using ih 2
          · simpa using ih 3
          · simpa using ih 1
      | @successor r hr ih =>
          intro k
          have classification := BandSuccessorClassification r hr
          dsimp at classification
          rcases classification with special | proper
          · fin_cases k
            · simp [special]
            · simpa using ih 0
            · simpa using ih 2
            · simpa using ih 3
          · rcases proper with ⟨_, larger0, larger2, larger3⟩
            fin_cases k
            · change 0 ≤ 2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1
              exact (ih 0).trans larger0.le
            · exact ih 0
            · exact ih 2
            · exact ih 3
    have hc : 0 ≤ (q j.succ).1 + (q 0).1 := by
      exact add_nonneg (nonnegative q hq j.succ) (nonnegative q hq 0)
    nlinarith
  have hgauss :
      BandVectors.1 (q j.succ) (q 0) +
          (q 0).2 * star (BandVectors.1 (q j.succ) (q 0)) =
        (2 : GaussianInt) * (q 0).1 * BandVectors.2 (q j.succ) (q 0) := by
    apply (mul_left_cancel₀ hv)
    calc
      BandVectors.1 (q j.succ) (q 0) *
          (BandVectors.1 (q j.succ) (q 0) +
            (q 0).2 * star (BandVectors.1 (q j.succ) (q 0))) =
          BandVectors.1 (q j.succ) (q 0) ^ 2 +
            (q 0).2 * (BandVectors.1 (q j.succ) (q 0) *
              star (BandVectors.1 (q j.succ) (q 0))) := by ring
      _ = (q 0).1 * ((q j.succ).2 + (q 0).2) := by
        rw [← Zsqrtd.norm_eq_mul_conj, hnorm, hident.1]
        push_cast
        ring
      _ = BandVectors.1 (q j.succ) (q 0) *
          ((2 : GaussianInt) * (q 0).1 * BandVectors.2 (q j.succ) (q 0)) := by
        rw [← hident.2]
        ring
  have hre := congr_arg Zsqrtd.re hgauss
  have him := congr_arg Zsqrtd.im hgauss
  simp? at hre him
  rw [hchild] at hre him
  have hrer :
      ((BandVectors.1 (q j.succ) (C.1.1)).re : ℝ) +
          ((C.1.1.2.re : ℝ) * (BandVectors.1 (q j.succ) (C.1.1)).re +
            (C.1.1.2.im : ℝ) * (BandVectors.1 (q j.succ) (C.1.1)).im) =
        2 * (C.1.1.1 : ℝ) * (BandVectors.2 (q j.succ) (C.1.1)).re := by
    exact_mod_cast hre
  have himr :
      ((BandVectors.1 (q j.succ) (C.1.1)).im : ℝ) +
          (-((C.1.1.2.re : ℝ) * (BandVectors.1 (q j.succ) (C.1.1)).im) +
            (C.1.1.2.im : ℝ) * (BandVectors.1 (q j.succ) (C.1.1)).re) =
        2 * (C.1.1.1 : ℝ) * (BandVectors.2 (q j.succ) (C.1.1)).im := by
    exact_mod_cast him
  have hcurv : 0 < (C.1.1.1 : ℝ) := by exact_mod_cast C.2
  rw [hmatrix]
  dsimp
  ext k
  fin_cases k
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.vecCons, Matrix.vecEmpty, Fin.cons, Fin.cases, Fin.induction,
      Fin.induction.go, hchild, -GaussianInt.intCast_re,
      -GaussianInt.intCast_im]
    field_simp [ne_of_gt hcurv]
    nlinarith [hrer]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.vecCons, Matrix.vecEmpty, Fin.cons, Fin.cases, Fin.induction,
      Fin.induction.go, hchild, -GaussianInt.intCast_re,
      -GaussianInt.intCast_im]
    field_simp [ne_of_gt hcurv]
    nlinarith [himr]

end ApollonianSuperharmonic

end
