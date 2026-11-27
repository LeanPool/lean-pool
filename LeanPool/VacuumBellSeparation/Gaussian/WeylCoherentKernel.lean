/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CanonicalThermalModel

/-!
# Actual Weyl expectation in a coherent vector

This evaluates the already constructed oscillator Weyl operator. The
phase is fixed by the repository's genuine Weyl representation, including
the factor two in the coherent displacement phase.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexConjugate

theorem oscillatorWeyl_coherent_diagonal (z w : ℂ) :
    inner ℂ (coherentVector w) (oscillatorWeyl z (coherentVector w)) =
      Complex.exp (((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) +
        2 * Complex.I * ((conj w * z).im : ℂ)) := by
  rw [oscillatorWeyl_coherentVector, inner_smul_right, inner_coherentVector,
    weylPhase, weylKernel, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp only [id_eq, RCLike.inner_apply', Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sq_norm, Complex.normSq_apply] <;> norm_num <;> ring

end VacuumBellSeparation.Gaussian
