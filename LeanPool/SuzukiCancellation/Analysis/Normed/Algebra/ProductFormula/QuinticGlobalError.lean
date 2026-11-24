/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.InteractionPicture
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalAsymptotics

/-!
# Global operator errors retaining quintic cancellation

The finite interaction product and midpoint quadrature combine to give the
continuous operator remainder, retaining the complete integral as its main term.

## Main results

* `norm_interactionProduct_sub_integral_le`: the global operator bound.
* `two_sided_norm_of_norm_sub_le`: the corresponding scalar enclosure.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError
open scoped RealScalar

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Global operator remainder.** Centered local control and the original
local norm bound imply the continuous cancellation estimate at every step size. -/
theorem norm_interactionProduct_sub_integral_le (G S L : A) (C alpha : ℝ)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (h : ℝ) (hh : 0 ≤ h)
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ quinticCenteredRemainder ‖L‖ C alpha h)
    (hstep : ‖S - exp (h • G)‖ ≤ h ^ 5 * ‖L‖ + h ^ 7 * C) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
      h ^ 4 • conjugationIntegral G L ((r : ℝ) * h)‖ ≤
        quinticGlobalRemainder ‖L‖ C alpha ‖⁅G, ⁅G, L⁆⁆‖ ((r : ℝ) * h) h r := by
  have hcap : ‖S - exp (h • G)‖ ≤ quinticStepBound ‖L‖ C h := by
    apply le_min _ hstep
    exact (norm_sub_le S _).trans (by linarith [hG h])
  have hd := norm_interactionProduct_sub_midpoint_le G S L hG hS h hlocal hcap r
  have hq := norm_midpointConjugationIntegral_sub_conjugationIntegral_le G L hG r h hh
  rw [quinticGlobalRemainder_eq _ _ _ _ _ _ _ rfl]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (h ^ 4 • midpointConjugationIntegral G L r h) _).trans
    (add_le_add hd ?_)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg hh 4)]
  exact mul_le_mul_of_nonneg_left hq (pow_nonneg hh 4)

variable {E : Type*} [NormedAddCommGroup E]

/-- An operator remainder bounds the norm from both sides. -/
theorem two_sided_norm_of_norm_sub_le (x y : E) {R : ℝ} (h : ‖x - y‖ ≤ R) :
    max 0 (‖y‖ - R) ≤ ‖x‖ ∧ ‖x‖ ≤ ‖y‖ + R := by
  constructor
  · apply max_le (norm_nonneg _)
    have hy := norm_sub_norm_le y x
    rw [norm_sub_rev] at hy
    linarith
  · linarith [norm_sub_norm_le x y]

end FQFP
