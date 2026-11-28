/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Polynomial
public import LeanPool.MathFin.Models.ModelFree.SVI.CriticalPoints
public import LeanPool.MathFin.Models.ModelFree.SVI.Derivatives

/-! # Durrleman's condition as a finite critical-point count

Part of the SVI polynomial-sign certificate (#174).

For `σ > 0`, positive variance and a nonconstant numerator polynomial (of degree at most ten),
`g(k) ≥ 0` for every `k` is equivalent to a positive leading coefficient, a nonnegative value at
`0`, and the absence of positive critical points at which the polynomial is negative
(`svi_finite_critical_criterion`). `four_query_count`: on any finite set, a signed combination of
four Tarski queries equals four times the number of points `c > 0` with `P c < 0`.

## Main definitions

* `tarskiQuery`: the Tarski query of `q` on a finite set of points, the sum of the signs of its
  values.
* `criticalRoots`: the distinct critical points of a polynomial, `P.derivative.roots.toFinset`.
* `badCriticalCount`: the number of distinct critical points `c > 0` of `P` at which `P` is
  negative.

## Main results

* `durrleman_eq_derivatives`: for `σ > 0`, `durrleman p k` is the expression built from the first
  and second derivatives of the variance.
* `svi_critical_value_criterion`: for `σ > 0`, positive variance and a nonconstant numerator
  polynomial, `durrleman p k ≥ 0` for all `k` iff the leading coefficient is positive, the value at
  `0` is nonnegative and no positive critical point has a negative value.
* `four_query_count`: on any finite set, a signed combination of four Tarski queries equals
  `4` times the number of points `c > 0` with `P c < 0`.
* `badCriticalCount_eq_zero_iff`: for `0 < deg P`, `badCriticalCount P = 0` iff no positive critical
  point of `P` has a negative value.
* `svi_finite_critical_criterion`: the criterion of `svi_critical_value_criterion` with the last
  condition replaced by `badCriticalCount (polynomial p) = 0`.

## Tags

Durrleman condition, critical points, Tarski query, SVI butterfly arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- Checked analytic/algebraic reduction through the critical-value criterion.
The remaining quantifier elimination is deliberately not assumed here. -/
theorem svi_critical_value_criterion (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) (hd : 0 < (polynomial p).degree) :
    (∀ k : ℝ, 0 ≤ durrleman p k) ↔
    0 < (polynomial p).leadingCoeff ∧ 0 ≤ (polynomial p).eval 0 ∧
      ¬ ∃ c : ℝ, 0 < c ∧ (polynomial p).derivative.eval c = 0 ∧
        (polynomial p).eval c < 0 := by
  rw [durrleman_nonneg_iff p hs hw]
  simp_rw [← eval_polynomial]
  exact polynomial_nonneg_criterion (polynomial p) hd

/-- The expression is built from the actual first and second derivatives. -/
theorem durrleman_eq_derivatives (p : Params) (hs : 0 < p.sigma) (k : ℝ) :
    durrleman p k =
      (1 - k * deriv (variance p) k / (2 * variance p k))^2 -
        (deriv (variance p) k)^2 / 4 * (1 / variance p k + 1 / 4) +
        deriv (deriv (variance p)) k / 2 := by
  rw [deriv_variance p hs, deriv_slope p hs]
  rfl

open scoped BigOperators

/-- The Tarski query of `q` on a finite set of points: the sum of the signs of its values. -/
noncomputable def tarskiQuery (roots : Finset ℝ) (q : ℝ → ℝ) : ℤ :=
  ∑ c ∈ roots, sign (q c)

/-- The four-query formula on any finite set, hence also on distinct critical
points. This theorem does not assume a trace/signature identity. -/
theorem four_query_count (roots : Finset ℝ) (P : ℝ → ℝ) :
    tarskiQuery roots (fun c ↦ c^2 * (P c)^2) +
    tarskiQuery roots (fun c ↦ c * (P c)^2) -
    tarskiQuery roots (fun c ↦ c^2 * P c) -
    tarskiQuery roots (fun c ↦ c * P c) =
    4 * ((roots.filter (fun c ↦ 0 < c ∧ P c < 0)).card : ℤ) := by
  classical
  unfold tarskiQuery
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [four_sign_selector]
  simp [← Finset.sum_filter, mul_comm]

/-- Distinct critical points, obtained by removing root multiplicities. -/
noncomputable def criticalRoots (P : Polynomial ℝ) : Finset ℝ := P.derivative.roots.toFinset

/-- The number of distinct critical points `c > 0` of `P` at which `P` is negative. -/
noncomputable def badCriticalCount (P : Polynomial ℝ) : ℕ :=
  ((criticalRoots P).filter (fun c ↦ 0 < c ∧ P.eval c < 0)).card

theorem badCriticalCount_eq_zero_iff (P : Polynomial ℝ) (hd : 0 < P.degree) :
    badCriticalCount P = 0 ↔
      ¬ ∃ c : ℝ, 0 < c ∧ P.derivative.eval c = 0 ∧ P.eval c < 0 := by
  classical
  have hf : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr hd))
  simp only [badCriticalCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    criticalRoots, Multiset.mem_toFinset, Polynomial.mem_roots hf, Polynomial.IsRoot]
  constructor
  · intro h ⟨c, hc, hf, hn⟩
    exact h hf ⟨hc, hn⟩
  · intro h c hf ⟨hc, hn⟩
    exact h ⟨c, hc, hf, hn⟩

/-- Endpoint signs and the vanishing finite count are equivalent to the original
smooth SVI condition. Matrix evaluation of this count is the remaining bridge. -/
theorem svi_finite_critical_criterion (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) (hd : 0 < (polynomial p).degree) :
    (∀ k : ℝ, 0 ≤ durrleman p k) ↔
    0 < (polynomial p).leadingCoeff ∧ 0 ≤ (polynomial p).eval 0 ∧
      badCriticalCount (polynomial p) = 0 := by
  rw [badCriticalCount_eq_zero_iff _ hd]
  exact svi_critical_value_criterion p hs hw hd

end SVI
end MathFin
