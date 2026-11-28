/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.CAPMEquilibrium
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Risk-parity portfolios from the log-barrier Lagrangian (first-principles)

The pre-existing `Choice/Portfolio/RiskParity.lean` states the 2-asset closed form
`w_1^{RP} = σ_2 / (σ_1 + σ_2)` and verifies the equal-risk-contribution
identity algebraically (no derivation from a variational principle).

This file derives the N-asset risk-parity / risk-budget conditions from the
first-order condition of the canonical convex programme used in the
risk-parity literature (Roncalli 2014, Maillard-Roncalli-Teïletche 2010):

  `min_w  (1/2) · w^T Σ w − ∑_i b_i · log(w_i)`,    `w_i > 0`.

The FOC is

  `(Σw)_i = b_i / w_i`,                              for every `i`,

equivalently `w_i · (Σw)_i = b_i` (risk contribution `RC_i` equals the
prescribed risk budget `b_i`). Risk parity is the special case `b_i = c`
constant — all assets contribute equally to variance.

## Why this is "first principles"

Risk parity was previously stated as an algebraic identity at closed-form
weights. This file shows it as the *output of an optimisation*: critical
points of the log-barrier-regularised variance minimisation satisfy the
risk-budget property. The 2-asset closed form `σ_2 / (σ_1 + σ_2)` has equal
risk contributions (`RiskParity.lean`; `isRiskParity_two_iff` shows it is the
only long-only budget portfolio that does), so it satisfies this FOC with the
uniform budget `b_i = RC_i = Var(w)/2`. For the budget `b_i = 1/N` the solution
is that portfolio rescaled, since `RC_i(t·w) = t²·RC_i(w)`; the rescaling is not
formalized here.

## Main definitions

* `riskContribution`: the contribution `wᵢ (Σw)ᵢ` of asset `i` to the portfolio variance.
* `IsRiskParity`: all assets have the same risk contribution.
* `IsRiskBudgetPortfolio`: each asset's risk contribution equals a prescribed budget `bᵢ`.
* `logBarrierObj`: the log-barrier objective `(1/2) wᵀ Σ w − ∑ᵢ bᵢ log wᵢ` whose critical points
  are the risk-budget portfolios.

## Main results

* `sum_riskContribution_eq_variance`: `∑ RC_i = w^T Σ w`.
* `isRiskBudget_of_log_barrier_FOC` (forward derivation): FOC `(Σw)_i =
  b_i / w_i` ⟹ risk-budget property.
* `isRiskParity_of_uniform_log_barrier_FOC`: specialisation with uniform
  budget ⟹ risk parity.
* `isRiskParity_iff_cross_product`: equivalent cross-product
  characterisation.

## Tags

risk parity, risk budgeting, log-barrier, equal risk contribution, Roncalli, first-order condition,
convex programme, MSC 91G10, MSC 90C25, JEL G11
-/

@[expose] public section

namespace MathFin

open Finset

/-- **Risk contribution of asset `i`** in portfolio `w` under covariance
matrix `Sg`: `RC_i := w_i · (Σw)_i`. The sum of risk contributions equals
the portfolio variance. -/
def riskContribution {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) : ℝ :=
  w i * marginalVariance s Sg w i

/-- **Sum-of-risk-contributions identity**: `∑_i RC_i = Var(w) = w · (Σw)`. -/
lemma sum_riskContribution_eq_variance
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    ∑ i ∈ s, riskContribution s Sg w i = portfolioVarN s w Sg := by
  rw [portfolioVarN_eq_sum_mul_marginalVariance]
  rfl

/-- **Equal-risk-contribution property ("risk parity")**: all assets
contribute the same amount of risk to portfolio variance, i.e., `RC_i = RC_j`
for every pair `(i, j) ∈ s × s`. -/
def IsRiskParity {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s,
    riskContribution s Sg w i = riskContribution s Sg w j

/-- **Risk-budget portfolio**: each asset's risk contribution matches a
prescribed budget `b_i`. Risk parity is the uniform-budget specialisation. -/
def IsRiskBudgetPortfolio {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w b : ι → ℝ) : Prop :=
  ∀ i ∈ s, riskContribution s Sg w i = b i

/-- **Forward derivation: risk-budget property from log-barrier Lagrangian
FOC**. The critical-point condition

  `(Σw)_i = b_i / w_i` for all `i ∈ s` with `w_i ≠ 0`,

(which is the FOC of `(1/2) w^T Σ w − ∑_i b_i log(w_i)`) implies the
risk-budget identity `w_i · (Σw)_i = b_i`. -/
theorem isRiskBudget_of_log_barrier_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w b : ι → ℝ)
    (h_pos : ∀ i ∈ s, w i ≠ 0)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = b i / w i) :
    IsRiskBudgetPortfolio s Sg w b := by
  intro i hi
  unfold riskContribution
  rw [h_FOC i hi, mul_div_assoc', mul_comm, mul_div_assoc, div_self (h_pos i hi), mul_one]

/-- **Risk parity from uniform-budget log-barrier FOC**: if the FOC holds
with the *same* constant `c` for every asset (uniform risk budget), then
the portfolio satisfies the equal-risk-contribution property. -/
theorem isRiskParity_of_uniform_log_barrier_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (c : ℝ)
    (h_pos : ∀ i ∈ s, w i ≠ 0)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = c / w i) :
    IsRiskParity s Sg w := by
  intro i hi j hj
  unfold riskContribution
  rw [h_FOC i hi, h_FOC j hj,
      mul_div_assoc', mul_comm (w i) c, mul_div_assoc, div_self (h_pos i hi), mul_one,
      mul_div_assoc', mul_comm (w j) c, mul_div_assoc, div_self (h_pos j hj), mul_one]

/-- **Cross-product characterisation of risk parity**: `RC_i = RC_j` is
literally `w_i · (Σw)_i = w_j · (Σw)_j`. This is the form used in numerical
solvers (project onto the equal-contribution hyperplane). -/
theorem isRiskParity_iff_cross_product
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    IsRiskParity s Sg w ↔
      ∀ i ∈ s, ∀ j ∈ s,
        w i * marginalVariance s Sg w i = w j * marginalVariance s Sg w j := by
  unfold IsRiskParity riskContribution
  rfl

/-- **Risk parity implies each `RC_i = Var(w) / |s|`**: at a risk-parity
portfolio, every asset contributes `1/N`-th of the total variance. -/
theorem riskContribution_eq_variance_div_card_of_riskParity
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (w : ι → ℝ) (i : ι) (hi : i ∈ s) (hs : s.Nonempty)
    (h_RP : IsRiskParity s Sg w) :
    riskContribution s Sg w i =
      portfolioVarN s w Sg / (s.card : ℝ) := by
  have h_card_pos : 0 < (s.card : ℝ) := by exact_mod_cast s.card_pos.mpr hs
  have h_card_ne : (s.card : ℝ) ≠ 0 := h_card_pos.ne'
  -- ∑ RC_j = card · RC_i (since all are equal)
  have h_sum : ∑ j ∈ s, riskContribution s Sg w j =
               (s.card : ℝ) * riskContribution s Sg w i := by
    have h_all_eq : ∀ j ∈ s,
        riskContribution s Sg w j = riskContribution s Sg w i := fun j hj ↦ h_RP j hj i hi
    rw [Finset.sum_congr rfl h_all_eq, Finset.sum_const, nsmul_eq_mul]
  rw [sum_riskContribution_eq_variance] at h_sum
  field_simp
  linarith

/-- **Log-barrier risk-parity objective**. The canonical convex programme whose
critical points are the risk-budget portfolios:

  `L(w) = (1/2) · wᵀ Σ w − ∑_i b_i · log(w_i)`.

Minimising `L` subject to `w > 0` is the standard risk-parity formulation
(Maillard–Roncalli–Teïletche 2010, Roncalli 2014). -/
noncomputable def logBarrierObj {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ)
    (b w : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * portfolioVarN s w Sg - ∑ i ∈ s, b i * Real.log (w i)

/-- **Directional derivative of the log-barrier objective** along coordinate
`j`. Freezing all weights except `w_j` and differentiating `L` in `w_j` at the
base point yields

  `∂L/∂w_j = (Σw)_j − b_j / w_j`.

The quadratic term contributes `(Σw)_j` (its `w_j`-gradient is `2·(Σw)_j` by
symmetry of `Σ`, halved), and the log-barrier term contributes `− b_j / w_j`. -/
theorem hasDerivAt_logBarrierObj_update
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Sg : ι → ι → ℝ) (b w : ι → ℝ)
    (j : ι) (hj : j ∈ s) (hSg : ∀ a c, Sg a c = Sg c a) (hwj : w j ≠ 0) :
    HasDerivAt (fun x ↦ logBarrierObj s Sg b (Function.update w j x))
      (marginalVariance s Sg w j - b j / w j) (w j) := by
  -- === derivative of the quadratic term ===
  -- coordinate factor:  d/dx (update w j x) k = [k = j]
  have hu : ∀ k, HasDerivAt (fun x ↦ Function.update w j x k)
      (if k = j then (1 : ℝ) else 0) (w j) := by
    intro k
    by_cases hk : k = j
    · rw [ite_eq_left hk]
      have hfun : (fun x ↦ Function.update w j x k) = fun x ↦ x := by
        funext x; rw [hk, Function.update_self]
      rw [hfun]; exact hasDerivAt_id (w j)
    · rw [ite_eq_right hk]
      have hfun : (fun x ↦ Function.update w j x k) = fun _ ↦ w k := by
        funext x; rw [Function.update_of_ne hk]
      rw [hfun]; exact hasDerivAt_const (w j) (w k)
  -- inner marginal factor:  d/dx ∑_l Sg k l · (update w j x) l = Sg k j
  have hv : ∀ k, HasDerivAt (fun x ↦ ∑ l ∈ s, Sg k l * Function.update w j x l)
      (Sg k j) (w j) := by
    intro k
    have hterm : ∀ l, HasDerivAt (fun x ↦ Sg k l * Function.update w j x l)
        (if l = j then Sg k j else 0) (w j) := by
      intro l
      by_cases hl : l = j
      · rw [ite_eq_left hl]
        have hfun : (fun x ↦ Sg k l * Function.update w j x l)
            = fun x ↦ Sg k l * x := by funext x; rw [hl, Function.update_self]
        rw [hfun, hl]
        simpa using (hasDerivAt_id (w j)).const_mul (Sg k j)
      · rw [ite_eq_right hl]
        have hfun : (fun x ↦ Sg k l * Function.update w j x l)
            = fun _ ↦ Sg k l * w l := by funext x; rw [Function.update_of_ne hl]
        rw [hfun]; exact hasDerivAt_const (w j) (Sg k l * w l)
    have hsum : HasDerivAt (fun x ↦ ∑ l ∈ s, Sg k l * Function.update w j x l)
        (∑ l ∈ s, if l = j then Sg k j else 0) (w j) :=
      HasDerivAt.fun_sum (fun l (_ : l ∈ s) ↦ hterm l)
    rw [Finset.sum_ite_eq' s j, ite_eq_left hj] at hsum
    exact hsum
  -- product rule per outer index k
  have hF : ∀ k, HasDerivAt
      (fun x ↦ Function.update w j x k * ∑ l ∈ s, Sg k l * Function.update w j x l)
      ((if k = j then (1 : ℝ) else 0)
          * (∑ l ∈ s, Sg k l * Function.update w j (w j) l)
        + Function.update w j (w j) k * Sg k j) (w j) :=
    fun k ↦ (hu k).mul (hv k)
  -- sum over k: derivative of the whole quadratic (pre-simplification)
  have hsum : HasDerivAt
      (fun x ↦ ∑ k ∈ s,
        Function.update w j x k * ∑ l ∈ s, Sg k l * Function.update w j x l)
      (∑ k ∈ s, ((if k = j then (1 : ℝ) else 0)
          * (∑ l ∈ s, Sg k l * Function.update w j (w j) l)
        + Function.update w j (w j) k * Sg k j)) (w j) :=
    HasDerivAt.fun_sum (fun k (_ : k ∈ s) ↦ hF k)
  -- identify that sum with `portfolioVarN ∘ update`
  have hfun : (fun x ↦ portfolioVarN s (Function.update w j x) Sg)
      = (fun x ↦ ∑ k ∈ s,
          Function.update w j x k * ∑ l ∈ s, Sg k l * Function.update w j x l) := by
    funext x; rw [portfolioVarN_eq_sum_mul_marginalVariance]; rfl
  -- simplify the derivative sum to `2 · (Σw)_j`
  have hderiv_eq :
      (∑ k ∈ s, ((if k = j then (1 : ℝ) else 0)
          * (∑ l ∈ s, Sg k l * Function.update w j (w j) l)
        + Function.update w j (w j) k * Sg k j))
        = 2 * marginalVariance s Sg w j := by
    simp only [Function.update_eq_self]
    rw [Finset.sum_add_distrib]
    have h1 : (∑ k ∈ s, (if k = j then (1 : ℝ) else 0) * ∑ l ∈ s, Sg k l * w l)
        = marginalVariance s Sg w j := by
      have hcongr : ∀ k ∈ s,
          (if k = j then (1 : ℝ) else 0) * (∑ l ∈ s, Sg k l * w l)
            = if k = j then (∑ l ∈ s, Sg k l * w l) else 0 := by
        intro k _; by_cases hk : k = j <;> simp [hk]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' s j, ite_eq_left hj]
      rfl
    have h2 : (∑ k ∈ s, w k * Sg k j) = marginalVariance s Sg w j := by
      unfold marginalVariance
      refine Finset.sum_congr rfl (fun k _ ↦ ?_)
      rw [hSg k j]; ring
    rw [h1, h2]; ring
  -- assemble: half the quadratic derivative
  have hPV : HasDerivAt (fun x ↦ portfolioVarN s (Function.update w j x) Sg)
      (2 * marginalVariance s Sg w j) (w j) := by
    rw [hfun, ← hderiv_eq]; exact hsum
  have hHalf : HasDerivAt
      (fun x ↦ (1 / 2 : ℝ) * portfolioVarN s (Function.update w j x) Sg)
      (marginalVariance s Sg w j) (w j) := by
    have h := hPV.const_mul (1 / 2 : ℝ)
    have he : (1 / 2 : ℝ) * (2 * marginalVariance s Sg w j)
        = marginalVariance s Sg w j := by ring
    rwa [he] at h
  -- === derivative of the log-barrier term ===
  have hLog : HasDerivAt
      (fun x ↦ ∑ i ∈ s, b i * Real.log (Function.update w j x i))
      (b j / w j) (w j) := by
    have hterm : ∀ i, HasDerivAt (fun x ↦ b i * Real.log (Function.update w j x i))
        (if i = j then b j / w j else 0) (w j) := by
      intro i
      by_cases hi : i = j
      · rw [ite_eq_left hi]
        have hfun : (fun x ↦ b i * Real.log (Function.update w j x i))
            = fun x ↦ b i * Real.log x := by
          funext x; rw [hi, Function.update_self]
        rw [hfun, hi, div_eq_mul_inv]
        exact (Real.hasDerivAt_log hwj).const_mul (b j)
      · rw [ite_eq_right hi]
        have hfun : (fun x ↦ b i * Real.log (Function.update w j x i))
            = fun _ ↦ b i * Real.log (w i) := by
          funext x; rw [Function.update_of_ne hi]
        rw [hfun]; exact hasDerivAt_const (w j) (b i * Real.log (w i))
    have hsumLog : HasDerivAt
        (fun x ↦ ∑ i ∈ s, b i * Real.log (Function.update w j x i))
        (∑ i ∈ s, if i = j then b j / w j else 0) (w j) :=
      HasDerivAt.fun_sum (fun i (_ : i ∈ s) ↦ hterm i)
    rw [Finset.sum_ite_eq' s j, ite_eq_left hj] at hsumLog
    exact hsumLog
  -- === combine ===
  unfold logBarrierObj
  exact hHalf.sub hLog

/-- **Critical-point characterisation of risk budgeting**: the log-barrier
objective is stationary in the `w_j`-direction (`HasDerivAt … 0`) *iff* the
risk-parity FOC `(Σw)_j = b_j / w_j` holds. This is the first-principles
statement — the FOC *assumed* in `isRiskBudget_of_log_barrier_FOC` is exactly
the condition for `w` to be a critical point of `L`. -/
theorem logBarrierObj_critical_iff_FOC
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Sg : ι → ι → ℝ) (b w : ι → ℝ)
    (j : ι) (hj : j ∈ s) (hSg : ∀ a c, Sg a c = Sg c a) (hwj : w j ≠ 0) :
    HasDerivAt (fun x ↦ logBarrierObj s Sg b (Function.update w j x)) 0 (w j) ↔
      marginalVariance s Sg w j = b j / w j := by
  have hd := hasDerivAt_logBarrierObj_update s Sg b w j hj hSg hwj
  constructor
  · intro h0
    have h := hd.unique h0
    linarith [h]
  · intro hfoc
    have hz : marginalVariance s Sg w j - b j / w j = 0 := by rw [hfoc]; ring
    rwa [hz] at hd

end MathFin
