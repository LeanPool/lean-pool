/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableAlgebra

/-!
# PotentialResolventIdentitiesReg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Pointwise resolvent and perturbation identities for the interior
representative of the potential resolvent, indexed by the regularity witness.
-/

/-!
# The pointwise resolvent identity of the potential resolvent

The resolvent identity of the potential resolvent is an identity between `L²`
classes.  Because each class has exactly one representative continuous on the
open domain, it becomes an identity at every point of the domain.

The statement is indexed by the interior regularity witness of the potential
resolvent.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

section IdentitiesReg

variable (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
  {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a)
  {C : ℝ} (hC : 0 ≤ C) (q : Vec d → ℝ)
  (hq : IsBoundedNonnegativePotential U q C)
  (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C) [NeZero d]

/-! ## The pointwise resolvent identity -/

omit [NeZero d] in
/-- The resolvent identity of the potential resolvent, applied to a datum. -/
theorem potentialResolvent_resolvent_identity_apply (mu nu : PositiveShift)
    (X : ScalarL2 U) :
    potentialResolvent a mu.property hlam hEll q hq X =
      potentialResolvent a nu.property hlam hEll q hq X +
        ((nu : ℝ) - (mu : ℝ)) • potentialResolvent a nu.property hlam hEll q hq
          (potentialResolvent a mu.property hlam hEll q hq X) := by
  have hid := potentialResolvent_resolvent_identity a nu.property mu.property
    hlam hEll q hq
  have happ := congrArg (fun T : ScalarL2 U →L[ℝ] ScalarL2 U => T X) hid
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply] at happ
  have hstep : potentialResolvent a nu.property hlam hEll q hq X -
      potentialResolvent a mu.property hlam hEll q hq X =
      ((mu : ℝ) - (nu : ℝ)) • potentialResolvent a nu.property hlam hEll q hq
        (potentialResolvent a mu.property hlam hEll q hq X) := happ
  have hsmul : ((mu : ℝ) - (nu : ℝ)) • potentialResolvent a nu.property hlam
        hEll q hq (potentialResolvent a mu.property hlam hEll q hq X) =
      -(((nu : ℝ) - (mu : ℝ)) • potentialResolvent a nu.property hlam hEll q hq
        (potentialResolvent a mu.property hlam hEll q hq X)) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hsmul] at hstep
  linear_combination (norm := module) -hstep


end IdentitiesReg

end

end DivergenceFormProcess.Form
