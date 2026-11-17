/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Iterated derivatives of `log ∘ f` at a normalized point

Generic calculus support (used for the polynomial growth of the derivatives of a smoothed
log-density, Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2, p. 5): the raw derivatives of
`log` at `1` are `(-1)^n n!`, and for `f` smooth and positive near `x` with `f x = 1` and
`‖D^i f(x)‖ ≤ D^i`, the Faà di Bruno bound gives `‖D^n (log ∘ f)(x)‖ ≤ (n!)² D^n`. Raw iterated
Fréchet derivatives, not Taylor coefficients.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- `D^{n+1} log (1) = (-1)^n n!`. -/
theorem iteratedDeriv_log_succ_one (n : ℕ) :
    iteratedDeriv (n + 1) Real.log 1 = (-1 : ℝ) ^ n * (n.factorial : ℝ) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) n (s := Set.univ) isOpen_univ
    (by trivial : (1 : ℝ) ∈ Set.univ)
  rw [iteratedDerivWithin_univ] at h
  have hderiv : deriv Real.log = fun x : ℝ => 1 / x := by
    funext x
    rw [Real.deriv_log, one_div]
  rw [iteratedDeriv_succ', hderiv, h]
  simp

/-- `‖D^{n+1} log (1)‖ = n!`. -/
theorem norm_iteratedFDeriv_log_succ_one (n : ℕ) :
    ‖iteratedFDeriv ℝ (n + 1) Real.log 1‖ = (n.factorial : ℝ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_log_succ_one]
  simp

/-- `‖D^i log (1)‖ ≤ n!` for every `i ≤ n` (order `0` gives `log 1 = 0`). -/
theorem norm_iteratedFDeriv_log_one_le_factorial {i n : ℕ} (hin : i ≤ n) :
    ‖iteratedFDeriv ℝ i Real.log 1‖ ≤ (n.factorial : ℝ) := by
  cases i with
  | zero =>
    simp only [norm_iteratedFDeriv_zero, Real.log_one, norm_zero]
    positivity
  | succ k =>
    rw [norm_iteratedFDeriv_log_succ_one]
    exact_mod_cast Nat.factorial_le (by omega : k ≤ n)

/--
**Local derivative bound for `log ∘ f`**: if `f` is smooth and positive on an open set `U ∋ x`
with `f x = 1` and `‖D^i f(x)‖ ≤ D^i` for `1 ≤ i ≤ n`, then `‖D^n (log ∘ f)(x)‖ ≤ (n!)² D^n`
(Faà di Bruno bound `norm_iteratedFDerivWithin_comp_le` with the outer bound `‖D^i log(1)‖ ≤ n!`).
Only local positivity is used; `log` is never differentiated at `0`. -/
theorem norm_iteratedFDeriv_log_comp_le_factorial_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hpos : ∀ y ∈ U, 0 < f y) (hone : f x = 1) {n : ℕ} {D : ℝ}
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (f y)) x‖ ≤ (n.factorial : ℝ) ^ 2 * D ^ n := by
  have ht : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hs : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono
      (by intro y hy; simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy.ne')
  have hmap : MapsTo f U (Set.Ioi (0 : ℝ)) := fun y hy => hpos y hy
  have hC :
    ∀ i : ℕ,
      i ≤ n → ‖iteratedFDerivWithin ℝ i Real.log (Set.Ioi (0 : ℝ)) (f x)‖ ≤ (n.factorial : ℝ) := by
    intro i hi
    rw [hone,
      iteratedFDerivWithin_eq_iteratedFDeriv ht
        (Real.contDiffAt_log.2 one_ne_zero : ContDiffAt ℝ i Real.log (1 : ℝ)) (by simp)]
    exact norm_iteratedFDeriv_log_one_le_factorial hi
  have hDw : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D ^ i := by
    intro i hi hin
    have hfi : ContDiffAt ℝ i f x :=
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (hU.mem_nhds hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs hfi hx]
    exact hD i hi hin
  have hcom : ContDiffOn ℝ ∞ (Real.log ∘ f) U := hlog.comp hf hmap
  have hcomAt : ContDiffAt ℝ n (Real.log ∘ f) x :=
    (hcom.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (hU.mem_nhds hx)
  have hbound :=
    norm_iteratedFDerivWithin_comp_le hlog hf
      (WithTop.coe_le_coe.mpr le_top : (n : WithTop ℕ∞) ≤ ∞) ht hs hmap hx hC hDw
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs hcomAt hx] at hbound
  simpa only [Function.comp_def, pow_two, mul_assoc] using hbound

end FunctionalInequalities.Analysis
