/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
# Cutoffs for whole-space transport pairings

The spatial cutoff used in the energy calculation has compact support,
equals one on the inner ball, and has a derivative bounded by the inverse
radius.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A cutoff equal to one on the radius `R` ball and supported within the
radius `2R` ball. -/
@[expose]
def regularisedEnergyCutoff (R : ℝ) : Vec3 → ℝ :=
  CKN.canonicalBallCutoff 0 R (2 * R)

/-- The energy cutoff is one in its inner ball. -/
theorem regularisedEnergyCutoff_eq_one_of_mem_ball
    (R : ℝ) (hR : 0 < R) (x : Vec3)
    (hx : x ∈ CKN.euclideanBall 0 R) :
    regularisedEnergyCutoff R x = 1 :=
  CKN.canonicalBallCutoff_eq_one_on_inner hR.le
    (by linarith only [hR]) hx

/-- The energy cutoff takes values in the unit interval. -/
theorem regularisedEnergyCutoff_mem_unitInterval (R : ℝ) (x : Vec3) :
    0 ≤ regularisedEnergyCutoff R x ∧ regularisedEnergyCutoff R x ≤ 1 :=
  ⟨CKN.canonicalBallCutoff_nonneg 0 R (2 * R) x,
    CKN.canonicalBallCutoff_le_one 0 R (2 * R) x⟩

/-- The energy cutoff is smooth for positive radius. -/
theorem regularisedEnergyCutoff_smooth (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedEnergyCutoff R) := by
  exact CKN.canonicalBallCutoff_smooth 0 hR.le (by linarith only [hR])

/-- The energy cutoff has compact support for positive radius. -/
theorem regularisedEnergyCutoff_compact (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (regularisedEnergyCutoff R) := by
  exact CKN.canonicalBallCutoff_hasCompactSupport hR.le
    (by linarith only [hR])

/-- Each coordinate derivative of the energy cutoff is bounded by the
inverse cutoff radius. -/
theorem regularisedEnergyCutoff_derivative_bound
    (R : ℝ) (hR : 0 < R) (i : Fin 3) (x : Vec3) :
    |fderiv ℝ (regularisedEnergyCutoff R) x (CKN.basisVec i)| ≤
      32 / R := by
  have hgrad := CKN.canonicalBallCutoff_gradient_bound
    (x₀ := (0 : Vec3)) (r := R) (R := 2 * R) hR.le
    (by linarith only [hR]) x
  have hcoord := CKN.abs_apply_le_vecEuclideanNorm
    (CKN.classicalGradient (regularisedEnergyCutoff R) x) i
  calc
    |fderiv ℝ (regularisedEnergyCutoff R) x (CKN.basisVec i)| ≤
        CKN.vecEuclideanNorm
          (CKN.classicalGradient (regularisedEnergyCutoff R) x) := by
      simpa [regularisedEnergyCutoff, CKN.classicalGradient_apply] using hcoord
    _ ≤ 32 / (2 * R - R) := hgrad
    _ = 32 / R := by ring

end CKN.Leray

end
