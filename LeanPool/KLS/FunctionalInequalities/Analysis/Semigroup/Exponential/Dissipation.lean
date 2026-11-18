/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction

/-!
# Energy dissipation along the orbit of a bounded symmetric operator

`Exponential/Contraction.lean` differentiates `u ↦ ‖exp (-u • L) y‖ ^ 2` once and concludes that
it is antitone (resolvent contraction).  This module differentiates the same orbit **twice** and
records the two
resulting quantitative estimates: for `L` bounded and symmetric, `u ≥ 0` and `v = exp (-u • L) y`,

* `two_mul_inner_exp_neg_smul_le`: `2 u ⟪L v, v⟫ ≤ ‖y‖ ² - ‖v‖ ²`;
* `two_mul_norm_apply_exp_neg_smul_sq_le`: `2 u ‖L v‖ ² ≤ ⟪L y, y⟫ - ⟪L v, v⟫`,
  which additionally needs `L` nonnegative.

Spectrally both are the elementary inequality `1 - exp (-x) ≥ x exp (-x)` for `x ≥ 0`, once at the
level of the norm and once at the level of the quadratic form.  The proofs use no spectral
calculus, no square root of `L` and no functional calculus: each estimate is the statement that an
explicit real function of `u` with value `0` at `u = 0` has nonnegative derivative
`4 u ‖L v‖ ²`, respectively `4 u ⟪L (L v), L v⟫`, on `[0, ∞)`.

## Why both levels are needed

Applied to the Yosida approximation `L_s` of `T†T` and passed to the limit `s ↓ 0`, the first
estimate gives `2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²` and the second gives
`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`.  Together with the density arguments of
`Generated/FormDomain.lean` those are exactly the positive-time regularity statements
`Generated/Smoothing.lean` proves for arbitrary `L²` data.

## Deliberately out of scope

Nothing here mentions a partially defined operator, an adjoint, the Yosida approximation, the
generated semigroup, the Markov property, Bakry–Émery calculus or Buser's inequality.  This is
bounded-operator material on a real Hilbert space: no measure, no log-concavity, no KLS quantity.
The sharp constants of the scalar maxima (`sup x exp (-x) = 1/e`) are **not** used or claimed.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Dissipation

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

omit [CompleteSpace H₀] in
/-- `L` commutes with its own exponential: `L (exp (-s • L) y) = exp (-s • L) (L y)`.

`Commute.exp_left` applied to `Commute (-s • L) L`. -/
theorem exp_neg_smul_apply_comm (L : H₀ →L[ℝ] H₀) (s : ℝ) (y : H₀) :
    L (NormedSpace.exp (-s • L) y) = NormedSpace.exp (-s • L) (L y) := by
  have hc : Commute (NormedSpace.exp (-s • L)) L :=
    ((Commute.refl L).smul_left (-s)).exp_left
  exact congrArg (fun A : H₀ →L[ℝ] H₀ => A y) hc.symm

/-- The orbit `s ↦ exp (-s • L) y` has derivative `-(L (exp (-s • L) y))`.

This is `hasDerivAt_exp_smul_apply` with the sign of the generator moved onto the parameter. -/
theorem hasDerivAt_exp_neg_smul_apply (L : H₀ →L[ℝ] H₀) (y : H₀) (u : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (-s • L) y)
      (-(L (NormedSpace.exp (-u • L) y))) u := by
  have h := hasDerivAt_exp_smul_apply (-L) y u
  have e : ∀ s : ℝ, s • (-L) = -s • L := fun s => by rw [smul_neg, neg_smul]
  simp only [e] at h
  simpa using h

/-- First derivative of the squared norm along the orbit: `-2 ⟪L v, v⟫`.

The quantitative form of the computation behind `antitone_normSq_exp_smul_neg`; symmetry of `L`
is not needed, only symmetry of the real inner product. -/
theorem hasDerivAt_norm_exp_neg_smul_sq (L : H₀ →L[ℝ] H₀) (y : H₀) (u : ℝ) :
    HasDerivAt (fun s : ℝ => ‖NormedSpace.exp (-s • L) y‖ ^ 2)
      (-(2 * ⟪L (NormedSpace.exp (-u • L) y), NormedSpace.exp (-u • L) y⟫)) u := by
  have h := (hasDerivAt_exp_neg_smul_apply L y u).inner ℝ (hasDerivAt_exp_neg_smul_apply L y u)
  have hfun : (fun s : ℝ => ‖NormedSpace.exp (-s • L) y‖ ^ 2)
      = fun s : ℝ => ⟪NormedSpace.exp (-s • L) y, NormedSpace.exp (-s • L) y⟫ := by
    funext s
    rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [inner_neg_left, inner_neg_right,
    real_inner_comm (L (NormedSpace.exp (-u • L) y)) (NormedSpace.exp (-u • L) y)]
  ring

/-- First derivative of the quadratic form along the orbit: `-2 ‖L v‖ ²`.

Here symmetry of `L` **is** used, together with `exp_neg_smul_apply_comm`. -/
theorem hasDerivAt_inner_exp_neg_smul (L : H₀ →L[ℝ] H₀)
    (hsymm : ∀ x z : H₀, ⟪L x, z⟫ = ⟪x, L z⟫) (y : H₀) (u : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪L (NormedSpace.exp (-s • L) y), NormedSpace.exp (-s • L) y⟫)
      (-(2 * ‖L (NormedSpace.exp (-u • L) y)‖ ^ 2)) u := by
  have hfun : (fun s : ℝ => ⟪L (NormedSpace.exp (-s • L) y), NormedSpace.exp (-s • L) y⟫)
      = fun s : ℝ => ⟪NormedSpace.exp (-s • L) (L y), NormedSpace.exp (-s • L) y⟫ := by
    funext s
    rw [exp_neg_smul_apply_comm]
  rw [hfun]
  have h := (hasDerivAt_exp_neg_smul_apply L (L y) u).inner ℝ
    (hasDerivAt_exp_neg_smul_apply L y u)
  refine h.congr_deriv ?_
  rw [← exp_neg_smul_apply_comm L u y, inner_neg_left, inner_neg_right,
    hsymm (L (NormedSpace.exp (-u • L) y)) (NormedSpace.exp (-u • L) y),
    real_inner_self_eq_norm_sq]
  ring

/-- **Norm-level dissipation.**  For `L` bounded and symmetric, `u ≥ 0` and
`v = exp (-u • L) y`,

`2 u ⟪L v, v⟫ ≤ ‖y‖ ² - ‖v‖ ²`.

The function `θ u = ‖y‖ ² - ‖v u‖ ² - 2 u ⟪L (v u), v u⟫` vanishes at `u = 0` and has derivative
`4 u ‖L (v u)‖ ² ≥ 0` on `[0, ∞)`: the two first-order terms cancel exactly, which is why the
estimate is a genuine second-order statement.  Nonnegativity of `L` is not needed. -/
theorem two_mul_inner_exp_neg_smul_le (L : H₀ →L[ℝ] H₀)
    (hsymm : ∀ x z : H₀, ⟪L x, z⟫ = ⟪x, L z⟫) (y : H₀) {u : ℝ} (hu : 0 ≤ u) :
    2 * u * ⟪L (NormedSpace.exp (-u • L) y), NormedSpace.exp (-u • L) y⟫
      ≤ ‖y‖ ^ 2 - ‖NormedSpace.exp (-u • L) y‖ ^ 2 := by
  set θ : ℝ → ℝ := fun s => ‖y‖ ^ 2 - ‖NormedSpace.exp (-s • L) y‖ ^ 2
    - 2 * s * ⟪L (NormedSpace.exp (-s • L) y), NormedSpace.exp (-s • L) y⟫ with hθ
  have hd : ∀ s : ℝ, HasDerivAt θ (4 * s * ‖L (NormedSpace.exp (-s • L) y)‖ ^ 2) s := by
    intro s
    have hN := hasDerivAt_norm_exp_neg_smul_sq L y s
    have hΦ := hasDerivAt_inner_exp_neg_smul L hsymm y s
    have hlin : HasDerivAt (fun r : ℝ => 2 * r) 2 s := by
      simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
    refine (((hasDerivAt_const s (‖y‖ ^ 2)).sub hN).sub (hlin.mul hΦ)).congr_deriv ?_
    ring
  have hdiff : Differentiable ℝ θ := fun s => (hd s).differentiableAt
  have hmono : MonotoneOn θ (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn fun x hx => ?_
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    have : (0 : ℝ) ≤ ‖L (NormedSpace.exp (-x • L) y)‖ ^ 2 := sq_nonneg _
    nlinarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  have h0 : NormedSpace.exp (-(0 : ℝ) • L) y = y := by simp
  simp only [hθ] at h
  rw [h0] at h
  linarith

/-- **Form-level dissipation.**  For `L` bounded, symmetric and nonnegative, `u ≥ 0` and
`v = exp (-u • L) y`,

`2 u ‖L v‖ ² ≤ ⟪L y, y⟫ - ⟪L v, v⟫`.

Same mechanism one level up: `σ u = ⟪L y, y⟫ - ⟪L (v u), v u⟫ - 2 u ‖L (v u)‖ ²` vanishes at
`u = 0` and has derivative `4 u ⟪L (L (v u)), L (v u)⟫ ≥ 0` on `[0, ∞)`.  Nonnegativity of `L`
is used exactly once, for that derivative's sign. -/
theorem two_mul_norm_apply_exp_neg_smul_sq_le (L : H₀ →L[ℝ] H₀)
    (hsymm : ∀ x z : H₀, ⟪L x, z⟫ = ⟪x, L z⟫) (hnonneg : ∀ x : H₀, 0 ≤ ⟪L x, x⟫) (y : H₀)
    {u : ℝ} (hu : 0 ≤ u) :
    2 * u * ‖L (NormedSpace.exp (-u • L) y)‖ ^ 2
      ≤ ⟪L y, y⟫ - ⟪L (NormedSpace.exp (-u • L) y), NormedSpace.exp (-u • L) y⟫ := by
  have hM : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ‖L (NormedSpace.exp (-r • L) y)‖ ^ 2)
      (-(2 * ⟪L (L (NormedSpace.exp (-s • L) y)), L (NormedSpace.exp (-s • L) y)⟫)) s := by
    intro s
    have h := hasDerivAt_norm_exp_neg_smul_sq L (L y) s
    have hfun : (fun r : ℝ => ‖NormedSpace.exp (-r • L) (L y)‖ ^ 2)
        = fun r : ℝ => ‖L (NormedSpace.exp (-r • L) y)‖ ^ 2 := by
      funext r
      rw [exp_neg_smul_apply_comm]
    rw [hfun] at h
    rw [← exp_neg_smul_apply_comm L s y] at h
    exact h
  set σ : ℝ → ℝ := fun s => ⟪L y, y⟫
    - ⟪L (NormedSpace.exp (-s • L) y), NormedSpace.exp (-s • L) y⟫
    - 2 * s * ‖L (NormedSpace.exp (-s • L) y)‖ ^ 2 with hσ
  have hd : ∀ s : ℝ, HasDerivAt σ
      (4 * s * ⟪L (L (NormedSpace.exp (-s • L) y)), L (NormedSpace.exp (-s • L) y)⟫) s := by
    intro s
    have hΦ := hasDerivAt_inner_exp_neg_smul L hsymm y s
    have hlin : HasDerivAt (fun r : ℝ => 2 * r) 2 s := by
      simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
    refine (((hasDerivAt_const s ⟪L y, y⟫).sub hΦ).sub (hlin.mul (hM s))).congr_deriv ?_
    ring
  have hdiff : Differentiable ℝ σ := fun s => (hd s).differentiableAt
  have hmono : MonotoneOn σ (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn fun x hx => ?_
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    have := hnonneg (L (NormedSpace.exp (-x • L) y))
    nlinarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  have h0 : NormedSpace.exp (-(0 : ℝ) • L) y = y := by simp
  simp only [hσ] at h
  rw [h0] at h
  linarith

end Dissipation

end FunctionalInequalities.Analysis.Semigroup
