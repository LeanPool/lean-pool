/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Endomorphisms

/-!
# RegCoeffFieldOperations

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Value operations on regular coefficient fields

This module supplies measurable constant value scaling and negation for
CoarseGraining's `RegCoeffField` carrier.  It also packages the value-scaled
triadic spatial dilation used by multiscale field layers.
-/

namespace Algsuperdiff.Probability

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- Scale every matrix value of a regular coefficient field by a fixed real
constant. -/
def scaleReg (c : ℝ) (a : RegCoeffField d) : RegCoeffField d :=
  c • a

/-- Negate every matrix value of a regular coefficient field. -/
def negReg (a : RegCoeffField d) : RegCoeffField d :=
  scaleReg (-1) a

@[simp]
theorem negReg_apply (a : RegCoeffField d) (x : Vec d) :
    negReg a x = -a x := by
  ext i j
  simp only [negReg, scaleReg, RegCoeffField.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.neg_apply, neg_one_mul]

/-- Apply the triadic spatial dilation at index `k` and scale the resulting
field values by `3 ^ (γ k)`. -/
def triadicLayerScaleReg (γ : ℝ) (k : ℤ) (a : RegCoeffField d) : RegCoeffField d :=
  scaleReg (Real.rpow 3 (γ * (k : ℝ))) (dilateReg k a)

end

end Algsuperdiff.Probability
