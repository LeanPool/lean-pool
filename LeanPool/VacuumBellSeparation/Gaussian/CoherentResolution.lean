/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.BargmannPointwise
public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentRepresentation

/-!
# Actual weak coherent resolution of the identity

The normalized coherent frame coordinate is `⟨z|x⟩/sqrt(π)` for complex
Lebesgue measure. It preserves the inner product after integration. The
identity follows from the constructed Bargmann isometry and the genuine
measure-preserving conjugation of the plane.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

/-- Coherent frame coordinate. -/
noncomputable def coherentFrameCoordinate (x : OscillatorSpace) (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ)⁻¹ * inner ℂ (coherentVector z) x

theorem bargmannFunction_conj (x : OscillatorSpace) (z : ℂ) :
    bargmannFunction x (conj z) = coherentFrameCoordinate x z := by
  rw [bargmannFunction, Complex.norm_conj, starRingEnd_self_apply,
    coherentFrameCoordinate, coherentVector, inner_smul_left,
    ← Complex.exp_conj, Complex.conj_ofReal, ← Complex.ofReal_exp,
    Complex.ofReal_div]
  ring_nf

theorem integral_inner_coherentFrameCoordinate (x y : OscillatorSpace) :
    (∫ z : ℂ, inner ℂ (coherentFrameCoordinate x z) (coherentFrameCoordinate y z)) =
      inner ℂ x y := by
  have h := Complex.conjLIE.measurePreserving.integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding
    (fun z : ℂ => inner ℂ (bargmannFunction x z) (bargmannFunction y z))
  simpa only [Complex.conjLIE_apply, bargmannFunction_conj,
    integral_inner_bargmannFunction] using h

theorem integrable_inner_coherentFrameCoordinate (x y : OscillatorSpace) :
    Integrable (fun z : ℂ =>
      inner ℂ (coherentFrameCoordinate x z) (coherentFrameCoordinate y z)) := by
  have h := Complex.conjLIE.measurePreserving.integrable_comp_of_integrable
    (integrable_inner_bargmannFunction x y)
  simpa only [Function.comp_def, Complex.conjLIE_apply, bargmannFunction_conj] using h

theorem integral_coherentFrameCoordinate_norm_sq (x : OscillatorSpace) :
    (∫ z : ℂ, ‖coherentFrameCoordinate x z‖ ^ 2) = ‖x‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (integral_inner_coherentFrameCoordinate x x)
  rw [← integral_re (integrable_inner_coherentFrameCoordinate x x)] at h
  simpa only [inner_self_eq_norm_sq] using h

theorem integrable_coherentFrameCoordinate_norm_sq (x : OscillatorSpace) :
    Integrable (fun z : ℂ => ‖coherentFrameCoordinate x z‖ ^ 2) := by
  have h := (integrable_inner_coherentFrameCoordinate x x).re
  simpa only [inner_self_eq_norm_sq] using h

end VacuumBellSeparation.Gaussian
