/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Response.PathDerivative

/-!
# PathODE

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The affine Grönwall step and its Young absorption

Source: ABK26, the integration and Young steps in the proof of
`e.J.sensitivity`.

The manuscript integrates the derivative bound

```
|∂_t J(t)| ≤ C E^{1/2} M^{1/2} + C ‖∇h‖ λ^{-1} M ,   M = max_{t∈[0,1]} J(t) ,
```

and then absorbs `M` by Young's inequality.  Formalizing the running maximum
`M` would require a compactness argument; the two lemmas below replace it by an
equivalent and strictly elementary route:

* `mul_sqrt_le_young_div` applies Young's inequality **pointwise in `t`**,
  turning the derivative bound into the affine differential inequality
  `y' ≤ m + c y`;
* `le_exp_mul_add_of_hasDerivAt_le` integrates that inequality exactly, by
  differentiating the integrating factor `e^{-c(t-t₁)} y(t) - m (t - t₁)` and
  observing it is nonincreasing.

The two together give the same closed form as the source: a factor
`1 + δ + C ‖∇h‖ λ^{-1}` on the base response and a `δ^{-1}`-weighted energy
term.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open Algsuperdiff.Section24.Sensitivity.Provider.Response

noncomputable section

/-- **Young's inequality in the square-root form.** -/
theorem mul_sqrt_le_young_div {A y θ : ℝ} (hy : 0 ≤ y) (hθ : 0 < θ) :
    A * Real.sqrt y ≤ A ^ 2 / (2 * θ) + θ / 2 * y := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ y = s ^ 2 :=
    ⟨Real.sqrt y, Real.sqrt_nonneg y, (Real.sq_sqrt hy).symm⟩
  rw [Real.sqrt_sq hs]
  have h2θ : 0 < 2 * θ := by linarith
  rw [div_add' _ _ _ h2θ.ne', le_div_iff₀ h2θ]
  nlinarith [sq_nonneg (A - θ * s)]

/-- **Exact integration of the affine differential inequality `y' ≤ m + c y`.**

No running maximum and no compactness are used: the integrating factor
`e^{-c(t-t₁)} y(t) - m (t - t₁)` has a nonpositive derivative on `[t₁, t₂]`. -/
theorem le_exp_mul_add_of_hasDerivAt_le {y y' : ℝ → ℝ} {c m t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ) (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ m + c * y τ) (ht : t₁ ≤ t₂) :
    y t₂ ≤ Real.exp (c * (t₂ - t₁)) * (y t₁ + m * (t₂ - t₁)) := by
  set e : ℝ → ℝ := fun τ => Real.exp (-(c * (τ - t₁))) with hedef
  have hepos : ∀ τ, 0 < e τ := fun τ => Real.exp_pos _
  have hederiv : ∀ τ, HasDerivAt e (-c * e τ) τ := by
    intro τ
    have hlin : HasDerivAt (fun s : ℝ => -(c * (s - t₁))) (-c) τ := by
      simpa using! (((hasDerivAt_id τ).sub_const t₁).const_mul c).neg
    simpa [hedef, mul_comm] using hlin.exp
  set z : ℝ → ℝ := fun τ => e τ * y τ - m * (τ - t₁) with hzdef
  set z' : ℝ → ℝ := fun τ => (-c * e τ * y τ + e τ * y' τ) - m with hz'def
  have hzderiv : ∀ τ, HasDerivAt z (z' τ) τ := by
    intro τ
    have hprod : HasDerivAt (fun s => e s * y s)
        (-c * e τ * y τ + e τ * y' τ) τ := (hederiv τ).mul (hderiv τ)
    have hlin : HasDerivAt (fun s : ℝ => m * (s - t₁)) m τ := by
      simpa using ((hasDerivAt_id τ).sub_const t₁).const_mul m
    simpa [hz'def] using! hprod.sub hlin
  have hzbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → z' τ ≤ 0 := by
    intro τ h1 h2
    have hey : e τ * y' τ ≤ e τ * (m + c * y τ) :=
      mul_le_mul_of_nonneg_left (hbound τ h1 h2) (hepos τ).le
    have hle1 : e τ ≤ 1 := by
      rw [hedef]
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ c * (τ - t₁) := mul_nonneg hc (by linarith)
      linarith
    have hstep : e τ * m - m ≤ 0 := by nlinarith [hepos τ, hle1, hm]
    rw [hz'def]
    nlinarith [hey, hstep]
  have hmain := le_add_of_hasDerivAt_le hzderiv hzbound ht
  have hz1 : z t₁ = y t₁ := by
    rw [hzdef, hedef]
    simp
  rw [hz1, zero_mul, add_zero] at hmain
  have hfinal : e t₂ * y t₂ ≤ y t₁ + m * (t₂ - t₁) := by
    rw [hzdef] at hmain
    linarith [hmain]
  have hinv : Real.exp (c * (t₂ - t₁)) * e t₂ = 1 := by
    rw [hedef, ← Real.exp_add]
    simp
  have hexppos : 0 < Real.exp (c * (t₂ - t₁)) := Real.exp_pos _
  have := mul_le_mul_of_nonneg_left hfinal hexppos.le
  calc y t₂ = (Real.exp (c * (t₂ - t₁)) * e t₂) * y t₂ := by rw [hinv, one_mul]
    _ = Real.exp (c * (t₂ - t₁)) * (e t₂ * y t₂) := by ring
    _ ≤ Real.exp (c * (t₂ - t₁)) * (y t₁ + m * (t₂ - t₁)) := this

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
