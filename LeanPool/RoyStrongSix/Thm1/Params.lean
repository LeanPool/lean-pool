/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The exponents of the transcendence construction

Work in the regime `1 ≤ q := d − n ≤ p := d₁` and `n ≥ 1`. All parameters are powers of one integer
base `β`, with integer exponents:

  `L₀ = β^{nQ}`, `T = β^{nθ}`, `L₁ = β^{n x₁}`, `S = β^{nσ}`,

where `K = p + 3n + d + 1`, `Q = (pd + 1)K`, `σ = qdK + 1`, `x₁ = Q − σ`, `θ = Q + 1`.

* `margin`: `nθ + 2n + d + 1 ≤ d₀Q + d₁x₁` (`d₀ = d − p`). The number of monomials `N ≍ β^{n(d₀Q +
d₁x₁)}`
  beats `T`, `L₀` and `L₁S` by a factor `β^{n+1}`. This absorbs every logarithm in the analytic
  contradiction (Step A).
* `x1_add_sigma`: `x₁ + σ = Q`, so `L₁ S = L₀`.
* `ratio_of_obstruction`: if the obstruction gives `cθ + ρσ ≤ d₀'Q + d₁'x₁` with
  `1 ≤ d' := d₀' + d₁' ≤ d`, then `c < d'` and `(d₁' + ρ) q ≤ p (d' − c)`. That is the ratio bound
  `(d₁' + ρ)/(d' − c) ≤ d₁/(d − n)`, exactly, with no limit.
* `log_dominated`: `C (1 + log β) < β` for all large `β`.
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.Thm1.Params

/-- The exponent data, given `p = d₁`, `q = d − n`, `n` and `d`. -/
structure Exps where
  /-- The multiplicative dimension parameter. -/
  p : ℕ
  /-- The codimension parameter. -/
  q : ℕ
  /-- The interpolation dimension parameter. -/
  n : ℕ
  /-- The total ambient dimension parameter. -/
  d : ℕ

namespace Exps

variable (X : Exps)

/-- An auxiliary margin scale separating the interpolation exponents. -/
def K : ℕ := X.p + 3 * X.n + X.d + 1
/-- The exponent controlling the additive polynomial degree. -/
def Q : ℕ := (X.p * X.d + 1) * X.K
/-- The exponent controlling the side length of the point grid. -/
def σ : ℕ := X.q * X.d * X.K + 1
/-- The exponent controlling the differentiation order. -/
def θ : ℕ := X.Q + 1
/-- The exponent controlling the multiplicative polynomial degree. -/
def x1 : ℕ := X.Q - X.σ

theorem K_pos : 1 ≤ X.K := by unfold K; omega

/-- `σ ≤ Q` when `q ≤ p`. -/
theorem sigma_le_Q (hqp : X.q ≤ X.p) : X.σ + X.K ≤ X.Q + 1 := by
  unfold σ Q
  have h1 : X.q * X.d * X.K ≤ X.p * X.d * X.K :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hqp)
  nlinarith [X.K_pos]

theorem x1_add_sigma (hqp : X.q ≤ X.p) : X.x1 + X.σ = X.Q := by
  have := X.sigma_le_Q hqp
  have := X.K_pos
  unfold x1; omega

theorem one_le_x1 (hqp : X.q ≤ X.p) (hn : 1 ≤ X.n) : 1 ≤ X.x1 := by
  have h := X.sigma_le_Q hqp
  have hK : 2 ≤ X.K := by unfold K; omega
  unfold x1; omega

/-- **The analytic margin.** -/
theorem margin (hq : 1 ≤ X.q) (hqp : X.q ≤ X.p) (hpd : X.p ≤ X.d) (hnd : X.n + X.q = X.d) :
    X.n * X.θ + 2 * X.n + X.d + 1 ≤ (X.d - X.p) * X.Q + X.p * X.x1 := by
  have hx := X.x1_add_sigma hqp
  -- `(d − p) Q + p x₁ = (n + q − p) Q + p (Q − σ) = (n + q) Q − p σ`
  have key : (X.d - X.p) * X.Q + X.p * X.x1 + X.p * X.σ = X.d * X.Q := by
    have : X.p * X.x1 + X.p * X.σ = X.p * X.Q := by rw [← Nat.mul_add, hx]
    have hdp : X.d - X.p + X.p = X.d := Nat.sub_add_cancel hpd
    calc (X.d - X.p) * X.Q + X.p * X.x1 + X.p * X.σ
        = (X.d - X.p) * X.Q + X.p * X.Q := by rw [add_assoc, this]
      _ = X.d * X.Q := by rw [← Nat.add_mul, hdp]
  -- `q Q − p σ − n = qK − p − n ≥ n + 1`
  have hQ : X.q * X.Q = X.p * X.σ - X.p + X.q * X.K := by
    unfold Q σ; ring_nf; omega
  have hpσ : X.p ≤ X.p * X.σ := Nat.le_mul_of_pos_right _ (by unfold σ; omega)
  have hqK : X.K ≤ X.q * X.K := Nat.le_mul_of_pos_left _ hq
  have hK : X.K = X.p + 3 * X.n + X.d + 1 := rfl
  have hθ : X.n * X.θ = X.n * X.Q + X.n := by unfold θ; ring
  have hdQ : X.d * X.Q = X.n * X.Q + X.q * X.Q := by rw [← hnd, Nat.add_mul]
  omega

/-- **The ratio bound from an obstruction.** -/
theorem ratio_of_obstruction (hqp : X.q ≤ X.p)
    {c d0' d1' ρ : ℕ} (hd' : 1 ≤ d0' + d1') (hdd : d0' + d1' ≤ X.d)
    (hob : c * X.θ + ρ * X.σ ≤ d0' * X.Q + d1' * X.x1) :
    c < d0' + d1' ∧ (d1' + ρ) * X.q ≤ X.p * (d0' + d1' - c) := by
  have hx := X.x1_add_sigma hqp
  set D := d0' + d1' with hD
  -- `c + (d₁' + ρ) σ + c Q ≤ D Q`
  have h1 : c + (d1' + ρ) * X.σ + c * X.Q ≤ D * X.Q := by
    have e1 : c * X.θ = c + c * X.Q := by unfold θ; ring
    have e2 : d1' * X.x1 + d1' * X.σ = d1' * X.Q := by rw [← Nat.mul_add, hx]
    have e3 : D * X.Q = d0' * X.Q + d1' * X.Q := by rw [hD, Nat.add_mul]
    nlinarith
  have hQpos : 1 ≤ X.Q := Nat.mul_pos (Nat.succ_pos _) X.K_pos
  have hcD : c < D := by
    by_contra h
    push Not at h
    have : D * X.Q ≤ c * X.Q := Nat.mul_le_mul_right _ h
    have : 1 ≤ c := le_trans hd' h
    omega
  refine ⟨hcD, ?_⟩
  set Z := D - c with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hZd : Z ≤ X.d := by omega
  have hDZ : D = Z + c := by omega
  -- `(d₁' + ρ) σ ≤ Z Q`
  have h2 : (d1' + ρ) * X.σ ≤ Z * X.Q := by
    have e1 : D * X.Q = Z * X.Q + c * X.Q := by rw [hDZ, Nat.add_mul]
    omega
  by_contra hne
  push Not at hne
  -- `(d₁' + ρ) q ≥ p Z + 1`, hence `(d₁' + ρ) σ q ≥ (p Z + 1) σ > q Z Q`
  have h3 : (X.p * Z + 1) * X.σ ≤ (d1' + ρ) * X.q * X.σ := Nat.mul_le_mul_right _ hne
  have h4 : X.q * Z * X.Q < (X.p * Z + 1) * X.σ := by
    -- `σ (pZ + 1) − q Z Q = q K (d − Z) + p Z + 1`
    have hdZ : X.d = Z + (X.d - Z) := by omega
    unfold σ Q
    have : X.q * Z * ((X.p * X.d + 1) * X.K) + X.p * Z + 1 ≤
        (X.p * Z + 1) * (X.q * X.d * X.K + 1) := by
      rw [hdZ]; ring_nf; nlinarith [Nat.zero_le (X.q * X.K * (X.d - Z))]
    omega
  have h5 : (d1' + ρ) * X.q * X.σ ≤ X.q * Z * X.Q := by
    calc (d1' + ρ) * X.q * X.σ = X.q * ((d1' + ρ) * X.σ) := by ring
      _ ≤ X.q * (Z * X.Q) := Nat.mul_le_mul_left _ h2
      _ = X.q * Z * X.Q := by ring
  omega

end Exps

/-- **Logarithms are dominated.** For every `C`, `C (1 + log β) < β` for all large `β`. -/
theorem log_dominated (C : ℝ) : ∃ β₀ : ℕ, ∀ β : ℕ, β₀ ≤ β → C * (1 + Real.log β) < β := by
  -- `log β ≤ 2 √β`, so it suffices that `C (1 + 2√β) < β`
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * |C| + 4)
  refine ⟨m ^ 2, fun β hβ => ?_⟩
  have hm0 : (0 : ℝ) < m := by linarith [abs_nonneg C]
  have hβpos : (0 : ℝ) < β := by
    have : (m : ℝ) ^ 2 ≤ β := by exact_mod_cast hβ
    nlinarith
  set r := Real.sqrt β with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hβpos
  have hrr : r * r = β := Real.mul_self_sqrt hβpos.le
  have hrm : (m : ℝ) ≤ r := by
    rw [hr]; apply Real.le_sqrt_of_sq_le; exact_mod_cast hβ
  have hlog : Real.log β ≤ 2 * r := by
    have : Real.log β = 2 * Real.log r := by
      rw [← hrr, Real.log_mul hr0.ne' hr0.ne']; ring
    rw [this]
    have := Real.log_le_sub_one_of_pos hr0
    linarith
  calc C * (1 + Real.log β) ≤ |C| * (1 + 2 * r) := by
        have h1 : 0 ≤ 1 + Real.log β := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ β by
            have : (1 : ℝ) ≤ m := by linarith [abs_nonneg C]
            nlinarith)
          linarith
        calc C * (1 + Real.log β) ≤ |C| * (1 + Real.log β) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) h1
          _ ≤ |C| * (1 + 2 * r) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    _ < r * r := by nlinarith [abs_nonneg C]
    _ = β := hrr

end StrongSix.Thm1.Params

end LeanPool
