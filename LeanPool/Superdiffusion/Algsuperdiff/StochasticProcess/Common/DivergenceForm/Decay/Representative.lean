/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Euclidean

/-!
# Representative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transferring a bound to a fixed continuous representative

The pointwise estimates of this directory end in an existential: some
function, continuous on a ball and almost everywhere equal to the solution
there, has a small value at the centre.  A consumer usually carries a
continuous representative of its own and needs the bound for that one.

The transfer is the standard fact that two functions continuous on an open
set and almost everywhere equal there agree at every point of it, because
Lebesgue measure is positive on nonempty open sets.  That fact is
`MeasureTheory.Measure.eqOn_open_of_ae_eq`; the statements below are its
specialization to Euclidean balls, in the shape the pointwise estimates hand
over.  Two representatives of the same solution are almost everywhere equal
to each other by transitivity, so no further hypothesis is needed.

## Main results

- `DivergenceFormProcess.Decay.eqOn_of_ae_eq_euclideanBall`
- `DivergenceFormProcess.Decay.abs_center_le_of_ae_eq_euclideanBall`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- Two functions continuous on a Euclidean ball and almost everywhere equal
there agree at every point of the ball. -/
theorem eqOn_of_ae_eq_euclideanBall {v w : Vec d → ℝ} {x : Vec d} {rho : ℝ}
    (hv : ContinuousOn v (euclideanBall x rho))
    (hw : ContinuousOn w (euclideanBall x rho))
    (hae : v =ᵐ[volume.restrict (euclideanBall x rho)] w) :
    Set.EqOn v w (euclideanBall x rho) :=
  Measure.eqOn_open_of_ae_eq hae (isOpen_euclideanBall x rho) hv hw

/-- A bound at the centre proved for one continuous representative holds for
every continuous representative on the same ball. -/
theorem abs_center_le_of_ae_eq_euclideanBall {v w : Vec d → ℝ} {x : Vec d}
    {rho C : ℝ} (hrho : 0 < rho)
    (hv : ContinuousOn v (euclideanBall x rho))
    (hw : ContinuousOn w (euclideanBall x rho))
    (hae : v =ᵐ[volume.restrict (euclideanBall x rho)] w)
    (hbound : |v x| ≤ C) : |w x| ≤ C := by
  rw [← eqOn_of_ae_eq_euclideanBall hv hw hae (center_mem_euclideanBall x hrho)]
  exact hbound

end DivergenceFormProcess.Decay
