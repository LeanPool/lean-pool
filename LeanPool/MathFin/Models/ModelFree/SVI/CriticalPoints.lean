/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-! # Nonnegativity of a polynomial on the positive half-line

Part of the SVI polynomial-sign certificate (#174).

A nonconstant real polynomial is nonnegative on `(0, ∞)` exactly when its leading coefficient is
positive, its constant term is nonnegative, and it has no critical point `c > 0` with a negative
value (`polynomial_nonneg_criterion`). `four_sign_selector` is the sign identity behind the four
Tarski queries.

## Main definitions

* `sign`: the sign of a real number as an integer, `1`, `-1` or `0`.

## Main results

* `exists_negative_critical`: a negative value of `P` at `x ∈ (0, R)`, with `P(0) ≥ 0` and
  `P(R) ≥ 0`, forces a critical point `c ∈ (0, R)` with `P(c) < 0`.
* `nonneg_iff_no_negative_critical`: for positive leading coefficient and `P(0) ≥ 0`, `P` is
  nonnegative on `(0, ∞)` iff it has no critical point `c > 0` with `P(c) < 0`.
* `polynomial_nonneg_criterion`: a nonconstant `P` is nonnegative on `(0, ∞)` iff its leading
  coefficient is positive, `P(0) ≥ 0`, and it has no critical point `c > 0` with `P(c) < 0`.
* `four_sign_selector`: `sign (c²v²) + sign (cv²) - sign (c²v) - sign (cv)` is `4` if `c > 0` and
  `v < 0`, and `0` otherwise.

## Tags

polynomial nonnegativity, critical point criterion, Tarski query, positive half-line, SVI,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Set Filter Polynomial

/-- A negative value between nonnegative endpoints forces a negative interior
critical value. No simplicity or nondegeneracy assumption is used. -/
theorem exists_negative_critical (P : ℝ[X]) (R x : ℝ)
    (hx : 0 < x) (hxR : x < R) (h0 : 0 ≤ P.eval 0)
    (hR : 0 ≤ P.eval R) (hxneg : P.eval x < 0) :
    ∃ c : ℝ, 0 < c ∧ c < R ∧ P.derivative.eval c = 0 ∧ P.eval c < 0 := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) R).Nonempty from ⟨x, hx.le, hxR.le⟩) P.continuous.continuousOn
  have hneg : P.eval c < 0 := lt_of_le_of_lt (hmin ⟨hx.le, hxR.le⟩) hxneg
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := le_antisymm (le_of_not_gt h) hc.1
    subst c
    linarith
  have hcR : c < R := by
    by_contra h
    have : c = R := le_antisymm hc.2 (le_of_not_gt h)
    subst c
    linarith
  refine ⟨c, hc0, hcR, ?_, hneg⟩
  have hlocal := hmin.isLocalMin (Icc_mem_nhds hc0 hcR)
  simpa only [Polynomial.deriv] using hlocal.deriv_eq_zero

/-- The critical-value criterion, assuming a positive leading coefficient.
This isolates the analytic part of the finite certificate. -/
theorem nonneg_iff_no_negative_critical (P : ℝ[X]) (hd : 0 < P.degree)
    (hl : 0 < P.leadingCoeff) (h0 : 0 ≤ P.eval 0) :
    (∀ x : ℝ, 0 < x → 0 ≤ P.eval x) ↔
    ¬ ∃ c : ℝ, 0 < c ∧ P.derivative.eval c = 0 ∧ P.eval c < 0 := by
  constructor
  · intro h ⟨c, hc, _, hn⟩
    exact (not_lt_of_ge (h c hc)) hn
  · intro h x hx
    by_contra hn
    have hxneg : P.eval x < 0 := lt_of_not_ge hn
    obtain ⟨z, hz⟩ := Filter.Eventually.exists_forall_of_atTop
      ((P.tendsto_atTop_of_leadingCoeff_nonneg hd hl.le).eventually_gt_atTop 0)
    let R := max z (x + 1)
    have hxR : x < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hR : 0 ≤ P.eval R := (hz R (le_max_left _ _)).le
    obtain ⟨c, hc, _, hder, hneg⟩ := exists_negative_critical P R x hx hxR h0 hR hxneg
    exact h ⟨c, hc, hder, hneg⟩

/-- The full nonconstant polynomial criterion, with both endpoint conditions. -/
theorem polynomial_nonneg_criterion (P : ℝ[X]) (hd : 0 < P.degree) :
    (∀ x : ℝ, 0 < x → 0 ≤ P.eval x) ↔
    0 < P.leadingCoeff ∧ 0 ≤ P.eval 0 ∧
      ¬ ∃ c : ℝ, 0 < c ∧ P.derivative.eval c = 0 ∧ P.eval c < 0 := by
  constructor
  · intro h
    have hl : 0 < P.leadingCoeff := by
      by_contra hn
      have ht := P.tendsto_atBot_of_leadingCoeff_nonpos hd (le_of_not_gt hn)
      obtain ⟨x, hx, hneg⟩ := ((eventually_gt_atTop (0 : ℝ)).and
        (ht.eventually_lt_atBot 0)).exists
      exact (not_lt_of_ge (h x hx)) hneg
    have h0 : 0 ≤ P.eval 0 := by
      have hc : IsClosed {x : ℝ | 0 ≤ P.eval x} := isClosed_le continuous_const P.continuous
      have hsub : Ioi (0 : ℝ) ⊆ {x : ℝ | 0 ≤ P.eval x} := fun x hx ↦ h x hx
      have hh := closure_minimal hsub hc
      apply hh
      simp only [closure_Ioi, mem_Ici, le_refl]
    exact ⟨hl, h0, (nonneg_iff_no_negative_critical P hd hl h0).mp h⟩
  · rintro ⟨hl, h0, hc⟩
    exact (nonneg_iff_no_negative_critical P hd hl h0).mpr hc

/-- The local sign selector used in the four Tarski queries. -/
noncomputable def sign (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

theorem four_sign_selector (c v : ℝ) :
    sign (c^2*v^2) + sign (c*v^2) - sign (c^2*v) - sign (c*v) =
      if 0 < c ∧ v < 0 then 4 else 0 := by
  rcases lt_trichotomy c 0 with hc | rfl | hc <;>
    rcases lt_trichotomy v 0 with hv | rfl | hv <;>
    simp [sign, *, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg,
      mul_pos_of_neg_of_neg, sq_pos_of_neg,
      not_lt_of_ge, le_of_lt]

end SVI
end MathFin
