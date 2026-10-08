/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.ComparisonLimits

/-!
# Commutator L2 Sq Nonneg

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The squared `L²` mass of the DiPerna–Lions commutator on a ball is nonnegative. -/
theorem commutatorL2Sq_nonneg {m : ℕ} (ε Rb : ℝ) (B : Vec m × ℝ → Vec m) (divB q : Vec m × ℝ → ℝ)
    (s : ℝ) : 0 ≤ commutatorL2Sq m ε Rb B divB q s := by
  unfold commutatorL2Sq
  refine MeasureTheory.setIntegral_nonneg measurableSet_closedBall ?_
  intro x hx
  apply sq_nonneg

end CIV
