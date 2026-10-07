/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselStokesOperator

/-!
# Continuity of the complete Sobolev mild nonlinearity

The complete nonlinear Stokes integrand varies continuously at every
strictly positive elapsed time when its velocity input is continuous.
-/

public section

open MeasureTheory FourierTransform Filter
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete H²ᵏ quadratic tensor is continuous in its velocity. -/
theorem regularisedBesselTensorQuadratic_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Continuous (regularisedBesselTensorQuadratic ρ ε hε k) := by
  let F := regularisedBesselTensorMap ρ ε hε k
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  change Continuous (fun u => F (E u) u)
  exact F.continuous₂.comp₂ E.continuous continuous_id

end CKN.Leray

end
