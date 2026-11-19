/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Inverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Resolvent.Form
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.VonNeumann

/-!
# Approximate eigenvectors at the bottom of `T†T` on `(ker T)ᗮ`

For a closed densely defined `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces and `A = T†T`, assume
the gap inequality `λ ‖y‖² ≤ ‖T y‖²` on `D(T) ∩ (ker T)ᗮ` with `λ > 0`. If a unit vector
`y ∈ D(T) ∩ (ker T)ᗮ` is almost optimal, `‖T y‖² ≤ λ (1 + η)`, then the solution `z ∈ D(A)` of
`(A + λ) z = 2 λ y` is orthogonal to `ker T`, satisfies `‖y - z‖ ≤ √(η / 8)` and is an approximate
eigenvector, `‖A z - λ z‖ ≤ λ √(η / 2)` (`exists_approx_eigenvector_of_gap`).

The argument: `z` is the weak resolvent solution `resolventDomain` at `s = λ⁻¹` with datum `2 y`,
so `z ∈ D(A)` with `A z = λ (2 y - z)`, and testing the weak equation against `k ∈ ker T` gives
`z ⊥ ker T`. With `w = y - z` and the form `q(u, v) = ⟪T u, T v⟫ - λ ⟪u, v⟫`, pairing
`A z - λ z = 2 λ w` with `w` gives `2 λ ‖w‖² = q(z, w) = q(y, w) - q(w, w)`, and the gap inequality
at `y / 2 - z = w - y / 2` gives `q(y, w) - q(w, w) ≤ q(y, y) / 4 ≤ λ η / 4`.

This replaces a first eigenvector of `A` on `(ker T)ᗮ` in Bizeul–Klartag–Lehec
(arXiv:2610.05474v1), Section 3. No
compactness and no spectral theorem are used, and no exact eigenvector is claimed to exist.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- The scalar core of the estimate: from the paired equation and the gap inequality at
`y / 2 - z`, `‖y - z‖² ≤ (‖T y‖² - λ ‖y‖²) / (8 λ)`, written without division. -/
private theorem mul_norm_sub_sq_le (T : H₀ →ₗ.[ℝ] H₁) {lam : ℝ} (y z : T.domain)
    (heq : 2 * lam * ‖(y : H₀) - (z : H₀)‖ ^ 2 =
      ⟪T z, T y - T z⟫ - lam * ⟪(z : H₀), (y : H₀) - (z : H₀)⟫)
    (hgap : lam * ‖(2 : ℝ)⁻¹ • (y : H₀) - (z : H₀)‖ ^ 2 ≤ ‖(2 : ℝ)⁻¹ • T y - T z‖ ^ 2) :
    8 * lam * ‖(y : H₀) - (z : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2 - lam * ‖(y : H₀)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq] at hgap heq ⊢
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    at hgap heq ⊢
  rw [real_inner_comm (T y) (T z), real_inner_comm (y : H₀) (z : H₀)] at hgap heq
  rw [real_inner_comm (y : H₀) (z : H₀)]
  nlinarith [hgap, heq]

/-- **Approximate eigenvectors at the bottom of `T†T` on `(ker T)ᗮ`.** Under the gap inequality
`λ ‖y‖² ≤ ‖T y‖²` on `D(T) ∩ (ker T)ᗮ`, a unit `y` there with `‖T y‖² ≤ λ (1 + η)` lies within
`√(η / 8)` of some `z ∈ D(T†T) ∩ (ker T)ᗮ` with `‖T†T z - λ z‖ ≤ λ √(η / 2)`.

The hypothesis `0 ≤ η` is not needed, since the gap inequality at `y`
already forces `λ ≤ ‖T y‖² ≤ λ (1 + η)`. -/
theorem exists_approx_eigenvector_of_gap (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {lam η : ℝ} (hlam : 0 < lam)
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2)
    (y : T.domain) (hy : ∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0)
    (hy1 : ‖(y : H₀)‖ = 1) (hTy : ‖T y‖ ^ 2 ≤ lam * (1 + η)) :
    ∃ z : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2) := by
  have hs : 0 < lam⁻¹ := inv_pos.mpr hlam
  set f : H₀ := (2 : ℝ) • (y : H₀) with hf
  set u : T.domain := resolventDomain T hT hs f with hu
  have hweak : WeakResolvent T lam⁻¹ f u := resolventDomain_spec T hT hs f
  have hmem : (u : H₀) ∈ (adjointComp T).domain :=
    mem_adjointComp_domain_resolventDomain T hT hs f
  let z : (adjointComp T).domain := ⟨(u : H₀), hmem⟩
  have hAz : adjointComp T z = lam • (f - (u : H₀)) := by
    have h := adjointComp_resolventDomain T hT hd hs f hmem
    rwa [inv_inv] at h
  have hzu : (⟨(z : H₀), z.2.2⟩ : T.domain) = u := rfl
  -- orthogonality to `ker T`
  have horth : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0 := by
    intro k hk
    have h := hweak k
    rw [hk, inner_zero_right, mul_zero, add_zero, hf, real_inner_smul_left, hy k hk,
      mul_zero] at h
    exact h
  -- the vector `B z = A z - λ z = 2 λ (y - z)`
  have hB : adjointComp T z - lam • (z : H₀) = (2 * lam) • ((y : H₀) - (u : H₀)) := by
    rw [hAz, hf]
    change lam • ((2 : ℝ) • (y : H₀) - (u : H₀)) - lam • (u : H₀) = _
    module
  -- the paired equation `2 λ ‖y - z‖² = q(z, y - z)`
  have heq : 2 * lam * ‖(y : H₀) - (u : H₀)‖ ^ 2 =
      ⟪T u, T y - T u⟫ - lam * ⟪(u : H₀), (y : H₀) - (u : H₀)⟫ := by
    have hpair : ⟪adjointComp T z, (y : H₀) - (u : H₀)⟫ = ⟪T u, T (y - u)⟫ :=
      inner_adjointComp hd z (y - u).2
    rw [LinearPMap.map_sub] at hpair
    have hcalc : ⟪adjointComp T z - lam • (z : H₀), (y : H₀) - (u : H₀)⟫ =
        2 * lam * ‖(y : H₀) - (u : H₀)‖ ^ 2 := by
      rw [hB, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [← hcalc, inner_sub_left, real_inner_smul_left]
    change ⟪adjointComp T z, (y : H₀) - (u : H₀)⟫ - lam * ⟪(u : H₀), (y : H₀) - (u : H₀)⟫ = _
    rw [hpair]
  -- the gap inequality at `y / 2 - z`
  have hgap' : lam * ‖(2 : ℝ)⁻¹ • (y : H₀) - (u : H₀)‖ ^ 2 ≤
      ‖(2 : ℝ)⁻¹ • T y - T u‖ ^ 2 := by
    have h := hgap ((2 : ℝ)⁻¹ • y - u) (by
      intro k hk
      change ⟪(2 : ℝ)⁻¹ • (y : H₀) - (u : H₀), (k : H₀)⟫ = 0
      rw [inner_sub_left, real_inner_smul_left, hy k hk, horth k hk, mul_zero, sub_zero])
    have hT : T ((2 : ℝ)⁻¹ • y - u) = (2 : ℝ)⁻¹ • T y - T u := by
      rw [LinearPMap.map_sub, LinearPMap.map_smul]
    rw [hT] at h
    exact h
  have hkey := mul_norm_sub_sq_le T y u heq hgap'
  rw [hy1] at hkey
  have hsq : ‖(y : H₀) - (u : H₀)‖ ^ 2 ≤ η / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hkey, hTy]
  refine ⟨z, horth, ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le hsq
  · rw [hB, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hle : ‖(y : H₀) - (u : H₀)‖ ≤ Real.sqrt (η / 8) := Real.le_sqrt_of_sq_le hsq
    have hsqrt : Real.sqrt (η / 2) = 2 * Real.sqrt (η / 8) := by
      rw [show η / 2 = 2 ^ 2 * (η / 8) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [hsqrt]
    nlinarith [hle, hlam]

end FunctionalInequalities.Analysis.Semigroup.Generated
