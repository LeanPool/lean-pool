/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Complex.Exponential

/-! # Peierls hopping amplitudes -/

@[expose] public section

namespace HubbardMoments

/-- The hopping coefficient at strength `t` and phase angle `angle`. -/
noncomputable def peierlsAmplitude (t angle : ℝ) : ℂ :=
  -(t : ℂ) * Complex.exp (angle * Complex.I)

/-- Reversing the phase angle conjugates the hopping coefficient. -/
theorem star_peierlsAmplitude (t angle : ℝ) :
    star (peierlsAmplitude t angle) = peierlsAmplitude t (-angle) := by
  rw [peierlsAmplitude, peierlsAmplitude, star_mul', star_neg, Complex.star_def,
    Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  simp only [mul_neg, neg_mul]

end HubbardMoments
