/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Contraction of negative operator exponentials

A bounded nonnegative operator on a complete real Hilbert space satisfies
`‖exp (-t • L) f‖ ≤ ‖f‖` for `t ≥ 0`. Self-adjointness is not required.
The proof differentiates the squared orbit norm. This is a bounded-operator
estimate; unbounded semigroup generation and the Markov property are separate.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Orbit

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/-- The orbit `t ↦ exp (t • A) f` of a bounded operator is differentiable, with derivative
`A (exp (t • A) f)`. This is `hasDerivAt_exp_smul_const'` evaluated at the fixed vector `f`. -/
theorem hasDerivAt_exp_smul_apply (A : H₀ →L[ℝ] H₀) (f : H₀) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) f) (A (NormedSpace.exp (t • A) f)) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t f)
  simpa using h

/-- Along the orbit `u t = exp (t • (-L)) f` of a nonnegative bounded operator `L`, the squared
norm `‖u t‖²` has derivative `-2 ⟪L (u t), u t⟫ ≤ 0` and is therefore antitone on all of `ℝ`.

Only nonnegativity of `L` and symmetry of the real inner product are used; self-adjointness of
`L` is not assumed. -/
theorem antitone_normSq_exp_smul_neg (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) (f : H₀) :
    Antitone fun t : ℝ => ‖NormedSpace.exp (t • (-L)) f‖ ^ 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2)
      (-(2 * ⟪L (NormedSpace.exp (t • (-L)) f), NormedSpace.exp (t • (-L)) f⟫)) t := by
    intro t
    have h := (hasDerivAt_exp_smul_apply (-L) f t).inner ℝ (hasDerivAt_exp_smul_apply (-L) f t)
    have hfun : (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2) =
        fun s : ℝ => ⟪NormedSpace.exp (s • (-L)) f, NormedSpace.exp (s • (-L)) f⟫ := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    rw [hfun]
    refine h.congr_deriv ?_
    rw [neg_apply, inner_neg_left, inner_neg_right,
      real_inner_comm (L (NormedSpace.exp (t • (-L)) f))]
    ring
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_
  rw [(hderiv t).deriv]
  have := hL (NormedSpace.exp (t • (-L)) f)
  linarith

/--
**Contraction of negative exponentials.** If `L` is a bounded nonnegative operator on a real Hilbert
space, then
`exp (-t • L)` is a contraction for every `t ≥ 0`, pointwise: `‖exp (-t • L) f‖ ≤ ‖f‖`.

No self-adjointness hypothesis is needed. -/
theorem norm_exp_neg_smul_apply_le (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {t : ℝ}
    (ht : 0 ≤ t) (f : H₀) : ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  have h := antitone_normSq_exp_smul_neg L hL f ht
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at h
  rw [neg_smul, ← smul_neg]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end Orbit

end FunctionalInequalities.Analysis.Semigroup
