/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakCarriers

/-!
# High-contrast homogenization: Provider.Response.ProfileMismatch

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Same-cell center mismatches

The two mismatch scalars retain the primal and coefficient-transpose centers
separately.  Each center component is subtracted from the same componentwise
annealed cell average that defines it, so both mismatches vanish exactly.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The primal same-cell mismatch after a fixed skew recentering. -/
@[expose]
def profilePrimalSameCellMismatch (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pMinus qMinus : Vec d) : ℝ :=
  abs
    (vecDot
        (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pMinus qMinus).2
        ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t (a.subSkew h0 hh0)
                pMinus qMinus)).1 i ∂P) -
          (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
            pMinus qMinus).1) +
      vecDot
        (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pMinus qMinus).1
        ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t (a.subSkew h0 hh0)
                pMinus qMinus)).2 i ∂P) -
          (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0)
            pMinus qMinus).2))

/-- The coefficient-transpose same-cell mismatch after the same recentering. -/
@[expose]
def profileAdjointSameCellMismatch (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (h0 : Mat d)
    (hh0 : IsSkewMat h0) (pPlus qPlus : Vec d) : ℝ :=
  abs
    (vecDot
        (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pPlus qPlus).2
        ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
              (diagonalWeakAdjointState hq t (a.subSkew h0 hh0)
                pPlus qPlus)).1 i ∂P) -
          (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
            pPlus qPlus).1) +
      vecDot
        (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
          pPlus qPlus).1
        ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
              (diagonalWeakAdjointState hq t (a.subSkew h0 hh0)
                pPlus qPlus)).2 i ∂P) -
          (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0)
            pPlus qPlus).2))

/-- The primal same-cell mismatch vanishes without a law-invariance
hypothesis. -/
theorem profilePrimalSameCellMismatch_eq_zero
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (h0 : Mat d) (hh0 : IsSkewMat h0)
    (pMinus qMinus : Vec d) :
    profilePrimalSameCellMismatch P hq t h0 hh0 pMinus qMinus = 0 := by
  unfold profilePrimalSameCellMismatch profilePrimalCenter
  simp only [sub_self, vecDot_zero_right, add_zero, abs_zero]

/-- The coefficient-transpose same-cell mismatch vanishes without a
law-invariance hypothesis. -/
theorem profileAdjointSameCellMismatch_eq_zero
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (h0 : Mat d) (hh0 : IsSkewMat h0)
    (pPlus qPlus : Vec d) :
    profileAdjointSameCellMismatch P hq t h0 hh0 pPlus qPlus = 0 := by
  unfold profileAdjointSameCellMismatch profileAdjointCenter
  simp only [sub_self, vecDot_zero_right, add_zero, abs_zero]

/-- Both independently loaded same-cell mismatches vanish exactly. -/
theorem profileSameCellMismatches_eq_zero
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (h0 : Mat d) (hh0 : IsSkewMat h0)
    (pMinus qMinus pPlus qPlus : Vec d) :
    profilePrimalSameCellMismatch P hq t h0 hh0 pMinus qMinus = 0 ∧
      profileAdjointSameCellMismatch P hq t h0 hh0 pPlus qPlus = 0 :=
  ⟨profilePrimalSameCellMismatch_eq_zero P hq t h0 hh0 pMinus qMinus,
    profileAdjointSameCellMismatch_eq_zero P hq t h0 hh0 pPlus qPlus⟩

end

end HCPolySupport.HighContrast.Response
