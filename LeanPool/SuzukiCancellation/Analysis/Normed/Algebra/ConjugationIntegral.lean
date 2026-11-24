/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Calculus.MidpointQuadrature
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.GroupedConjugation

/-!
# Integrals and midpoint sums of conjugation orbits

The continuous and discrete coefficients retain each conjugated element as
an element of the algebra. Under two-sided exponential contraction bounds,
the midpoint error is controlled by the norm of one double commutator.

## Main definitions

* `conjugationIntegral`: the continuous interaction coefficient.
* `midpointConjugationIntegral`: its finite midpoint sum.

## Main results

* `norm_expSMulConj_sub_linear_le`: the translated quadratic remainder.
* `norm_midpointConjugationIntegral_sub_conjugationIntegral_le`: the quadrature bound.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory Finset
open scoped RealScalar

namespace TrotterError

section Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The integral of the conjugation orbit `e^(-x G) L e^(x G)` from zero to `t`. -/
def conjugationIntegral (G L : A) (t : ℝ) : A :=
  ∫ x in 0..t, expSMulConj (-G) L x

/-- The midpoint sum of a conjugation orbit over `r` intervals of length `h`. -/
def midpointConjugationIntegral (G L : A) (r : ℕ) (h : ℝ) : A :=
  h • ∑ k ∈ range r, expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h)

/-- The conjugation integral over a zero-length interval vanishes. -/
@[simp] lemma conjugationIntegral_zero (G L : A) : conjugationIntegral G L 0 = 0 := by
  simp [conjugationIntegral]

/-- A midpoint sum with no cells vanishes. -/
@[simp] lemma midpointConjugationIntegral_zero (G L : A) (h : ℝ) :
    midpointConjugationIntegral G L 0 h = 0 := by
  simp [midpointConjugationIntegral]

/-- A midpoint sum with zero step vanishes. -/
@[simp] lemma midpointConjugationIntegral_zero_step (G L : A) (r : ℕ) :
    midpointConjugationIntegral G L r 0 = 0 := by
  simp [midpointConjugationIntegral]

/-- A single midpoint cell evaluates the orbit at its center. -/
@[simp] lemma midpointConjugationIntegral_one (G L : A) (h : ℝ) :
    midpointConjugationIntegral G L 1 h = h • expSMulConj (-G) L (h / 2) := by
  simp [midpointConjugationIntegral, div_eq_mul_inv, mul_comm]

end Definitions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Addition of times composes conjugations by the same generator. -/
lemma expSMulConj_add (G L : A) (x y : ℝ) :
    expSMulConj G L (x + y) = expSMulConj G (expSMulConj G L y) x := by
  simp only [expSMulConj]
  rw [← exp_smul_mul_exp_smul G x y, show -(x + y) = -y + -x by ring,
    ← exp_smul_mul_exp_smul G (-y) (-x)]
  simp only [mul_assoc]

/-- The first-order Taylor expansion of a conjugation orbit about any real
base point has the exact double-commutator remainder bound. -/
theorem norm_expSMulConj_sub_linear_le (G L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (c x : ℝ) :
    ‖expSMulConj G L x - expSMulConj G L c -
      (x - c) • expSMulConj G ⁅G, L⁆ c‖ ≤
        ‖⁅G, ⁅G, L⁆⁆‖ / 2 * (x - c) ^ 2 := by
  have hr := norm_expSMulConj_sub_sum_le_of_le_one G L hG 2 (by norm_num) (x - c)
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_smul, pow_one, Nat.factorial_one,
    ad_pow_succ, one_apply_eq_self, LieAlgebra.ad_apply] at hr
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hr
  rw [sq_abs] at hr
  have heq : expSMulConj G L x - expSMulConj G L c -
      (x - c) • expSMulConj G ⁅G, L⁆ c =
      expSMulConjLin G c (expSMulConj G L (x - c) - L - (x - c) • ⁅G, L⁆) := by
    rw [map_sub, map_sub, map_smul]
    change _ = expSMulConj G (expSMulConj G L (x - c)) c -
      expSMulConj G L c - (x - c) • expSMulConj G ⁅G, L⁆ c
    rw [← expSMulConj_add, add_sub_cancel]
  rw [heq]
  change ‖expSMulConj G _ c‖ ≤ _
  rw [norm_expSMulConj_eq_of_le_one G _ hG]
  convert hr using 1
  · rw [sub_add_eq_sub_sub]
  · ring

/-- **Conjugation midpoint bound.** The midpoint integral error over `r`
equal cells is bounded by `t h² / 24` times the double-commutator norm,
where `t = r h`. -/
theorem norm_midpointConjugationIntegral_sub_conjugationIntegral_le (G L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (r : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ‖midpointConjugationIntegral G L r h -
      conjugationIntegral G L ((r : ℝ) * h)‖ ≤
        ((r : ℝ) * h) * h ^ 2 * ‖⁅G, ⁅G, L⁆⁆‖ / 24 := by
  have hneg : ∀ t : ℝ, ‖exp (t • (-G))‖ ≤ 1 := by
    intro t
    simpa only [smul_neg, neg_smul] using hG (-t)
  have hr := norm_midpoint_sum_sub_integral_le (expSMulConj (-G) L)
    (continuous_expSMulConj (-G) L) r h ‖⁅G, ⁅G, L⁆⁆‖ (fun k _ ↦ ?_)
  · calc
      _ ≤ (r : ℝ) * h ^ 3 * ‖⁅G, ⁅G, L⁆⁆‖ / 24 := hr
      _ = _ := by ring
  have hc := norm_midpoint_smul_sub_integral_le (expSMulConj (-G) L)
    (continuous_expSMulConj (-G) L) ((k : ℝ) * h) h ‖⁅G, ⁅G, L⁆⁆‖ hh
    (expSMulConj (-G) ⁅-G, L⁆ ((k : ℝ) * h + h / 2))
    (fun x _ ↦ ?_)
  · simpa only [show (k : ℝ) * h + h / 2 = ((k : ℝ) + 1 / 2) * h by ring,
      show (k : ℝ) * h + h = ((k : ℝ) + 1) * h by ring] using hc
  have hdouble : ⁅-G, ⁅-G, L⁆⁆ = ⁅G, ⁅G, L⁆⁆ := by
    simp only [Ring.lie_def]
    noncomm_ring
  simpa only [hdouble] using
    norm_expSMulConj_sub_linear_le (-G) L hneg ((k : ℝ) * h + h / 2) x

end TrotterError
