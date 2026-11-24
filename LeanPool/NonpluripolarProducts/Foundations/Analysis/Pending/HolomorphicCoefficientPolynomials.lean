/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Polynomials with holomorphic coefficients

Tools for the local elimination argument in `AnalyticProjectionWeierstrass`,
where a Weierstrass polynomial `t^d + ∑_{k<d} a_k(z) t^k` and the
remainders of Weierstrass division are treated as polynomials in `t` whose coefficients
depend holomorphically on `z`.

* `holOnSubring U`: the ring of functions `E → ℂ` complex differentiable on `U`, with
  evaluation `evalAt U z` at a point.
* `differentiableOn_resultant_map`: for polynomials `P, Q` over that ring, the resultant
  (with fixed formal degrees) of the evaluated polynomials `P(z), Q(z)` is holomorphic in
  `z` on `U`.  By `Polynomial.resultant_map_map` it is the evaluation of the resultant
  computed in the ring, which is an element of the ring.
* `norm_lt_of_weierstrass_root`: the roots of `t^d + ∑_{k<d} a_k t^k` lie in the disc of
  radius `ε ≤ 1` once every `‖a_k‖ < ε^d / d`.
-/

@[expose] public section

open Polynomial

namespace SGPT.Foundations.Analysis.Pending.HolomorphicCoefficientPolynomials

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Functions `E → ℂ` complex differentiable on `U`, as a subring of `E → ℂ`. -/
def holOnSubring (U : Set E) : Subring (E → ℂ) where
  carrier := {f | DifferentiableOn ℂ f U}
  mul_mem' hf hg := hf.mul hg
  one_mem' := differentiableOn_const 1
  add_mem' hf hg := hf.add hg
  zero_mem' := differentiableOn_const 0
  neg_mem' hf := hf.neg

/-- Evaluation at `z` on the ring of functions differentiable on `U`. -/
def evalAt (U : Set E) (z : E) : holOnSubring U →+* ℂ :=
  (Pi.evalRingHom (fun _ : E => ℂ) z).comp (holOnSubring U).subtype

@[simp] theorem evalAt_apply (U : Set E) (z : E) (f : holOnSubring U) :
    evalAt U z f = (f : E → ℂ) z := rfl

/-- The polynomial `∑_{k<N} a_k T^k` over the ring of functions differentiable on `U`. -/
def ofCoeffs (U : Set E) (N : ℕ) (a : ℕ → E → ℂ) (ha : ∀ k, DifferentiableOn ℂ (a k) U) :
    (holOnSubring U)[X] :=
  ∑ k ∈ Finset.range N, C (⟨a k, ha k⟩ : holOnSubring U) * X ^ k

theorem map_ofCoeffs (U : Set E) (N : ℕ) (a : ℕ → E → ℂ)
    (ha : ∀ k, DifferentiableOn ℂ (a k) U) (z : E) :
    (ofCoeffs U N a ha).map (evalAt U z) = ∑ k ∈ Finset.range N, C (a k z) * X ^ k := by
  simp [ofCoeffs, Polynomial.map_sum]

/-- **Resultants of polynomials with holomorphic coefficients are holomorphic.** -/
theorem differentiableOn_resultant_map (U : Set E) (P Q : (holOnSubring U)[X]) (m n : ℕ) :
    DifferentiableOn ℂ
      (fun z => resultant (P.map (evalAt U z)) (Q.map (evalAt U z)) m n) U := by
  have h : (fun z => resultant (P.map (evalAt U z)) (Q.map (evalAt U z)) m n) =
      ((resultant P Q m n : holOnSubring U) : E → ℂ) := by
    funext z
    rw [resultant_map_map, evalAt_apply]
  rw [h]
  exact (resultant P Q m n).2

/-- **Root bound for Weierstrass-type polynomials.**  If `0 < ε ≤ 1` and every coefficient
satisfies `‖a_k‖ * d < ε ^ d`, every root `t` of `t^d + ∑_{k<d} a_k t^k` has `‖t‖ < ε`. -/
theorem norm_lt_of_weierstrass_root {d : ℕ} {a : ℕ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : ∀ k < d, ‖a k‖ * d < ε ^ d) {t : ℂ}
    (ht : t ^ d + ∑ k ∈ Finset.range d, a k * t ^ k = 0) : ‖t‖ < ε := by
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at ht
  have ht0 : 0 < ‖t‖ := hε.trans_le hlt
  -- `ε^(d-1) ‖t‖^k ≤ ‖t‖^(d-1)` for `k < d`
  have hpow : ∀ k < d, ε ^ (d - 1) * ‖t‖ ^ k ≤ ‖t‖ ^ (d - 1) := by
    intro k hkd
    calc ε ^ (d - 1) * ‖t‖ ^ k ≤ ε ^ (d - 1 - k) * ‖t‖ ^ k := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hε.le hε1 (Nat.sub_le _ _)) (by positivity)
      _ ≤ ‖t‖ ^ (d - 1 - k) * ‖t‖ ^ k := by gcongr
      _ = ‖t‖ ^ (d - 1) := by rw [← pow_add]; congr 1; omega
  have hsum : ‖t‖ ^ d = ‖∑ k ∈ Finset.range d, a k * t ^ k‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left ht, norm_neg]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ε ^ (d - 1) * ‖t‖ ^ d < ε ^ d * ‖t‖ ^ (d - 1) := by
    rw [hsum]
    calc ε ^ (d - 1) * ‖∑ k ∈ Finset.range d, a k * t ^ k‖
        ≤ ∑ k ∈ Finset.range d, ‖a k‖ * (ε ^ (d - 1) * ‖t‖ ^ k) := by
          refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow]
          nlinarith [norm_nonneg (a k), pow_nonneg (norm_nonneg t) k,
            pow_nonneg hε.le (d - 1)]
      _ ≤ ∑ k ∈ Finset.range d, ‖a k‖ * ‖t‖ ^ (d - 1) :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hpow k (Finset.mem_range.mp hk)) (norm_nonneg _)
      _ < ∑ k ∈ Finset.range d, ε ^ d / d * ‖t‖ ^ (d - 1) := by
          refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hd⟩ fun k hk => ?_
          have := ha k (Finset.mem_range.mp hk)
          have hlt' : ‖a k‖ < ε ^ d / d := by rw [lt_div_iff₀ hdR]; exact this
          exact mul_lt_mul_of_pos_right hlt' (pow_pos ht0 _)
      _ = ε ^ d * ‖t‖ ^ (d - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hd1 : d = d - 1 + 1 := by omega
  have : ε ^ d * ‖t‖ ^ (d - 1) ≤ ε ^ (d - 1) * ‖t‖ ^ d := by
    rw [hd1, pow_succ, pow_succ, Nat.add_sub_cancel]
    have := mul_le_mul_of_nonneg_left hlt (mul_nonneg (pow_nonneg hε.le (d - 1))
      (pow_nonneg ht0.le (d - 1)))
    linarith
  linarith

end

end SGPT.Foundations.Analysis.Pending.HolomorphicCoefficientPolynomials
