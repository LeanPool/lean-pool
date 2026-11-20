/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Exponentials of bounded operators on a complex Banach space

This module collects the facts about the exponential `NormedSpace.exp (t • B)` of a
bounded complex-linear operator `B : X →L[ℂ] X` that the abstract Hille–Yosida
development uses and that Mathlib does not supply.  Nothing here refers to the
project's operator interfaces.

Four groups of statements are proved.

* **Size.**  `norm_exp_le` compares the exponential series with the real exponential
  series term by term and gives `‖exp B‖ ≤ Real.exp ‖B‖`, the bound on which every
  uniform estimate of the Yosida approximants rests.  Mathlib proves this for
  quaternions only.  `exp_real_smul_one` evaluates the exponential of a real multiple
  of the identity, and `norm_exp_sub_smul_one_le` combines the two into the shifted
  bound `‖exp (B - c • 1)‖ ≤ Real.exp (-c) * Real.exp ‖B‖` used for the Yosida
  generator `r ^ 2 • R r - r • 1`.

* **The semigroup law along a real ray.**  `exp_add_smul` is
  `exp ((s + t) • B) = exp (s • B) * exp (t • B)`; the scalars are real, because the
  time variable of a semigroup is real, while the operators stay complex-linear.

* **Time differentiability.**  `hasDerivAt_exp_apply` differentiates the orbit
  `u ↦ exp (u • B) x` of a vector.  Because `HasDerivAt.clm_apply` insists that the
  operator family be linear over the same field as the time variable, the real-linear
  avatar `expR B s := (exp (s • B)).restrictScalars ℝ` is introduced, differentiated in
  `hasDerivAt_expR`, and used in `hasDerivAt_conjugate` to differentiate the
  interpolation `u ↦ exp ((t - u) • C) (exp (u • B) x)` between two operator
  exponentials — the telescoping identity behind the Cauchy estimate that makes the
  approximants converge.

* **Commutation.**  `exp_commute` propagates a commutation `Commute B C` to the
  exponential `exp (t • B)`.

Throughout, `exp` abbreviates the operator exponential `NormedSpace.exp` (the module
opens `NormedSpace`); the real exponential is always written `Real.exp`.

`NormedAlgebra ℚ (X →L[ℂ] X)` does not synthesize, so the two proofs that call
`NormedSpace.exp_add_of_commute` install it locally by restriction of scalars along
`ℚ → ℂ`, exactly as Mathlib itself does; it is never introduced as a global instance.
-/

@[expose] public section

namespace FastDynamo

namespace HilleYosida

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/--
The operator exponential is dominated by the real exponential of the operator norm,
`‖exp B‖ ≤ Real.exp ‖B‖`.

Both sides are expanded as series, `exp B = ∑' n, (n !)⁻¹ • B ^ n` and
`Real.exp ‖B‖ = ∑' n, (n !)⁻¹ • ‖B‖ ^ n`, and compared term by term through
`‖(n !)⁻¹ • B ^ n‖ = (n !)⁻¹ ‖B ^ n‖ ≤ (n !)⁻¹ ‖B‖ ^ n`.  The submultiplicativity
`‖B ^ n‖ ≤ ‖B‖ ^ n` is available only for `n ≠ 0`, so the constant term is treated
separately by `‖1‖ ≤ 1` (an equality would be false for `X = 0`).  Completeness of `X`
is not needed.
-/
theorem norm_exp_le (B : X →L[ℂ] X) : ‖NormedSpace.exp B‖ ≤ Real.exp ‖B‖ := by
  have hexp : NormedSpace.exp B = ∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • B ^ n := by
    rw [exp_eq_tsum ℂ]
  have hsum : Summable fun n : ℕ ↦ ‖((n.factorial : ℂ))⁻¹ • B ^ n‖ :=
    norm_expSeries_summable' (𝕂 := ℂ) B
  have hRsum : Summable fun n : ℕ ↦ ‖((n.factorial : ℝ))⁻¹ • ‖B‖ ^ n‖ :=
    norm_expSeries_summable' (𝕂 := ℝ) ‖B‖
  have hRsum' : Summable fun n : ℕ ↦ ((n.factorial : ℝ))⁻¹ • ‖B‖ ^ n := by
    simpa using hRsum.of_norm
  have hreal : Real.exp ‖B‖ = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • ‖B‖ ^ n := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  rw [hexp, hreal]
  refine (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_mono hsum hRsum' ?_)
  intro n
  change ‖((n.factorial : ℂ))⁻¹ • B ^ n‖ ≤ ((n.factorial : ℝ))⁻¹ • ‖B‖ ^ n
  rw [norm_smul]
  simp only [norm_inv, Complex.norm_natCast, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simpa [hn, ContinuousLinearMap.one_def] using
      ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)
  · gcongr
    exact norm_pow_le' B hn

omit [CompleteSpace X] in
/--
The exponential of a real multiple of the identity operator is the real exponential
times the identity: `exp (r • 1) = Real.exp r • 1`.  This is the commutation of
`NormedSpace.exp` with the algebra map `ℝ → (X →L[ℂ] X)`, whose image is exactly the
real multiples of the identity.  Completeness of `X` is not needed.
-/
theorem exp_real_smul_one (r : ℝ) :
    NormedSpace.exp (r • (1 : X →L[ℂ] X)) = Real.exp r • (1 : X →L[ℂ] X) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := X →L[ℂ] X) r
  simpa [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using h.symm

/--
The semigroup law of the exponential along the real ray through a fixed operator:
`exp ((s + t) • B) = exp (s • B) * exp (t • B)`.  The two factors commute because both
are real multiples of the same operator `B`.  The scalars are real — the time variable
of a semigroup is real — while `B` remains complex-linear; the rational normed algebra
structure demanded by `NormedSpace.exp_add_of_commute` is installed locally by
restriction of scalars.
-/
theorem exp_add_smul (B : X →L[ℂ] X) (s t : ℝ) :
    NormedSpace.exp ((s + t) • B) = NormedSpace.exp (s • B) * NormedSpace.exp (t • B) := by
  let +nondep : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ (X →L[ℂ] X)
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl B).smul_left s).smul_right t)

/--
The exponential of an operator shifted by a real multiple of the identity obeys
`‖exp (B - c • 1)‖ ≤ Real.exp (-c) * Real.exp ‖B‖`.

The shift commutes with `B`, so the exponential splits as
`exp B * exp (-(c • 1)) = Real.exp (-c) • exp B`; the two factors are then estimated by
`norm_exp_le` and by `‖1‖ ≤ 1`.  With `B = r ^ 2 • R r` and `c = r` this is the uniform
bound on the exponential of a Yosida generator.
-/
theorem norm_exp_sub_smul_one_le (B : X →L[ℂ] X) (c : ℝ) :
    ‖NormedSpace.exp (B - c • (1 : X →L[ℂ] X))‖ ≤ Real.exp (-c) * Real.exp ‖B‖ := by
  let +nondep : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ (X →L[ℂ] X)
  have hcomm : Commute B (-(c • (1 : X →L[ℂ] X))) := by
    simp [Commute, SemiconjBy]
  have hsplit : NormedSpace.exp (B - c • (1 : X →L[ℂ] X))
      = NormedSpace.exp B * NormedSpace.exp (-(c • (1 : X →L[ℂ] X))) := by
    rw [sub_eq_add_neg]
    exact exp_add_of_commute hcomm
  rw [hsplit, ← neg_smul, exp_real_smul_one]
  calc ‖NormedSpace.exp B * (Real.exp (-c) • (1 : X →L[ℂ] X))‖
      ≤ ‖NormedSpace.exp B‖ * ‖Real.exp (-c) • (1 : X →L[ℂ] X)‖ := norm_mul_le _ _
    _ ≤ Real.exp ‖B‖ * (Real.exp (-c) * 1) := by
        gcongr
        · exact norm_exp_le B
        · rw [norm_smul]
          gcongr
          · simp [abs_of_pos (Real.exp_pos (-c))]
          · simpa [ContinuousLinearMap.one_def] using
              ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)
    _ = Real.exp (-c) * Real.exp ‖B‖ := by ring

/--
The real-linear avatar `expR B s` of the operator exponential `exp (s • B)`: the same
map on `X`, remembered only as a continuous real-linear map.  It exists because
`HasDerivAt.clm_apply`, the product rule for an operator family applied to a moving
vector, requires the operators to be linear over the field of the time variable, here
`ℝ`, whereas `exp (s • B)` is complex-linear.
-/
noncomputable def expR (B : X →L[ℂ] X) (s : ℝ) : X →L[ℝ] X :=
  (NormedSpace.exp (s • B)).restrictScalars ℝ

/--
The real-linear avatar is differentiable in time, with derivative
`(exp (s • B) * B).restrictScalars ℝ`: the derivative of `s ↦ exp (s • B)` in the
operator algebra, transported by the continuous linear restriction-of-scalars map.
-/
theorem hasDerivAt_expR (B : X →L[ℂ] X) (s : ℝ) :
    HasDerivAt (fun u : ℝ ↦ expR B u)
      ((NormedSpace.exp (s • B) * B).restrictScalars ℝ) s := by
  have h : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • B)) (NormedSpace.exp (s • B) * B) s :=
    (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) B s).hasDerivAt
  exact (ContinuousLinearMap.restrictScalarsL ℂ X X ℝ ℝ).hasFDerivAt.comp_hasDerivAt s h

/--
The orbit `u ↦ exp (u • B) x` of a vector under the exponential semigroup generated by
`B` is differentiable at every real time `t`, with derivative `exp (t • B) (B x)`: the
abstract Cauchy problem `x' = B x`, `x 0 = x`, is solved by the exponential.  The
derivative of the operator family is evaluated at `x` through the continuous linear
evaluation map.
-/
theorem hasDerivAt_exp_apply (B : X →L[ℂ] X) (t : ℝ) (x : X) :
    HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • B) x) (NormedSpace.exp (t • B) (B x)) t := by
  have h : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • B)) (NormedSpace.exp (t • B) * B) t :=
    (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) B t).hasDerivAt
  have h2 := ((ContinuousLinearMap.apply ℂ X x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def, mul_apply_eq_comp] using h2

omit [CompleteSpace X] in
/--
An operator commuting with `B` commutes with every exponential `exp (t • B)`, `t` real.
This is how the commutation of two Yosida approximants, and the commutation of an
approximant with a resolvent, survive exponentiation.  Completeness of `X` is not
needed.
-/
theorem exp_commute {B C : X →L[ℂ] X} (hc : Commute B C) (t : ℝ) :
    Commute (NormedSpace.exp (t • B)) C :=
  (hc.smul_left t).exp_left

/--
The product rule for the interpolation between two exponential semigroups: the curve
`u ↦ exp ((t - u) • C) (exp (u • B) x)`, which joins `exp (t • C) x` at `u = 0` to
`exp (t • B) x` at `u = t`, is differentiable at every `s`, with derivative
`-exp ((t - s) • C) (C (exp (s • B) x)) + exp ((t - s) • C) (exp (s • B) (B x))`.

Integrating this derivative over `[0, t]` is the telescoping identity that compares two
exponential semigroups, and hence the Yosida approximants with each other.  The
operator factor is differentiated through its real-linear avatar `expR`, since the time
variable is real while the operators are complex-linear.
-/
theorem hasDerivAt_conjugate (B C : X →L[ℂ] X) (t : ℝ) (x : X) (s : ℝ) :
    HasDerivAt (fun u : ℝ ↦ expR C (t - u) (NormedSpace.exp (u • B) x))
      (-(NormedSpace.exp ((t - s) • C) (C (NormedSpace.exp (s • B) x)))
        + NormedSpace.exp ((t - s) • C) (NormedSpace.exp (s • B) (B x))) s := by
  have h1 : HasDerivAt (fun u : ℝ ↦ expR C (t - u))
      (-((NormedSpace.exp ((t - s) • C) * C).restrictScalars ℝ)) s := by
    have hsub : HasDerivAt (fun u : ℝ ↦ t - u) (-1 : ℝ) s :=
      HasDerivAt.const_sub t (hasDerivAt_id s)
    have h := HasDerivAt.scomp s (hasDerivAt_expR C (t - s)) hsub
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • B) x) (NormedSpace.exp (s • B) (B x)) s :=
    hasDerivAt_exp_apply B s x
  have h3 := HasDerivAt.clm_apply h1 h2
  simpa [expR, mul_apply_eq_comp] using h3

end HilleYosida

end FastDynamo
