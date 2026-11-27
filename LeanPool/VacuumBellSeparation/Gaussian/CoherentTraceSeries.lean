/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentResolution

/-!
# Justified coherent integral interchange

The actual L² frame gives the integral Cauchy--Schwarz bound. A summable
series of products of vector norms then justifies exchanging a series of
frame inner products and a Bochner integral. No formal trace interchange
or implicit integrability assumption is used.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory

theorem memLp_coherentFrameCoordinate (x : OscillatorSpace) :
    MemLp (coherentFrameCoordinate x) 2 (volume : Measure ℂ) := by
  have h := (memLp_bargmannFunction x).comp_measurePreserving
    Complex.conjLIE.measurePreserving
  have he : bargmannFunction x ∘ Complex.conjLIE = coherentFrameCoordinate x := by
    funext z
    exact bargmannFunction_conj x z
  rw [he] at h
  exact h

theorem integral_norm_inner_coherentFrameCoordinate_le (x y : OscillatorSpace) :
    (∫ z : ℂ, ‖inner ℂ (coherentFrameCoordinate x z) (coherentFrameCoordinate y z)‖) ≤
      ‖x‖ * ‖y‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (f := coherentFrameCoordinate x) (g := coherentFrameCoordinate y)
    (by simpa using memLp_coherentFrameCoordinate x)
    (by simpa using memLp_coherentFrameCoordinate y)
  simp only [Real.rpow_two, integral_coherentFrameCoordinate_norm_sq,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)] at h
  simpa only [RCLike.inner_apply', norm_mul, Complex.norm_conj] using h

theorem hasSum_integral_inner_coherentFrameCoordinate {u v : ℕ → OscillatorSpace}
    (huv : Summable fun n => ‖u n‖ * ‖v n‖) :
    HasSum (fun n => inner ℂ (u n) (v n))
      (∫ z : ℂ, ∑' n, inner ℂ (coherentFrameCoordinate (u n) z)
        (coherentFrameCoordinate (v n) z)) := by
  have hs : Summable fun n => ∫ z : ℂ,
      ‖inner ℂ (coherentFrameCoordinate (u n) z) (coherentFrameCoordinate (v n) z)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _)
      (fun n => integral_norm_inner_coherentFrameCoordinate_le (u n) (v n)) huv
  simpa only [integral_inner_coherentFrameCoordinate] using
    hasSum_integral_of_summable_integral_norm
      (fun n => integrable_inner_coherentFrameCoordinate (u n) (v n)) hs

end VacuumBellSeparation.Gaussian
