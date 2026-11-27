/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalDomains

/-!
# The actual commuting thermal inverse-power sandwich

For two one-mode thermal densities in the same number basis, the quadratic
form of `σ^(-τ/2) ρ σ^(-τ/2)` is defined on the actual dense range of
`σ^(τ/2)`. When `p < q^τ`, a convergent rank-one series supplies its unique
bounded extension and its finite positive trace. No bounded inverse of a
faithful density is assumed. This is the commuting one-mode specialization
of Appendix A.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

omit [CompleteSpace E] in
/-- Bounded operators are determined by their values on a genuine Hilbert
basis, using convergence of the basis expansion. -/
theorem continuousLinearMap_eq_of_hilbertBasis (b : HilbertBasis ι ℂ E)
    {A B : E →L[ℂ] E} (h : ∀ i, A (b i) = B (b i)) : A = B := by
  ext x
  have hA := (b.hasSum_repr x).mapL A
  have hB := (b.hasSum_repr x).mapL B
  have hA' : HasSum (fun i => b.repr x i • B (b i)) (A x) := by
    simpa only [map_smul, h] using hA
  have hB' : HasSum (fun i => b.repr x i • B (b i)) (B x) := by
    simpa only [map_smul] using hB
  exact hA'.unique hB'

/-- The inverse-power sandwich coefficients. Their summability is proved
on the strict trace domain below, and is not hidden in the definition. -/
noncomputable def thermalSandwichWeight (p q τ : ℝ) (n : ℕ) : ℝ :=
  thermalWeight p n / thermalWeight q n ^ τ

/-- Continuous linear map for the thermal sandwich, of type `OscillatorSpace →L[ℂ]
OscillatorSpace`. -/
noncomputable def thermalSandwich (p q τ : ℝ) :
    OscillatorSpace →L[ℂ] OscillatorSpace :=
  diagonalOperator numberBasis (thermalSandwichWeight p q τ)

theorem thermalSandwichWeight_geometric {p q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) :
    thermalSandwichWeight p q τ n =
      ((1 - p) / (1 - q) ^ τ) * (p / q ^ τ) ^ n := by
  rw [thermalSandwichWeight, thermalWeight_rpow hq₀ hq₁, thermalWeight,
    div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasSum_thermalSandwichWeight {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) :
    HasSum (thermalSandwichWeight p q τ)
      (((1 - p) / (1 - q) ^ τ) / (1 - p / q ^ τ)) := by
  have hqτ : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  have hr₀ : 0 ≤ p / q ^ τ := div_nonneg hp₀ hqτ.le
  have hr₁ : p / q ^ τ < 1 := (div_lt_one hqτ).mpr hpq
  have h := (hasSum_geometric_of_lt_one hr₀ hr₁).mul_left ((1 - p) / (1 - q) ^ τ)
  have he : thermalSandwichWeight p q τ =
      (fun n => ((1 - p) / (1 - q) ^ τ) * (p / q ^ τ) ^ n) :=
    funext (thermalSandwichWeight_geometric hq₀.le hq₁)
  rw [he]
  simpa only [div_eq_mul_inv] using h

theorem thermalSandwich_nonneg {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) :
    0 ≤ thermalSandwich p q τ := by
  apply diagonalOperator_nonneg
  intro n
  exact div_nonneg
    (mul_nonneg (sub_nonneg.mpr hp₁.le) (pow_nonneg hp₀ n))
    (Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ n) τ).le

theorem thermalSandwich_apply_numberBasis {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hq₀ : 0 < q) (hq₁ : q < 1) (hpq : p < q ^ τ) (n : ℕ) :
    thermalSandwich p q τ (numberBasis n) =
      thermalSandwichWeight p q τ n • numberBasis n :=
  diagonalOperator_apply_basis numberBasis
    (hasSum_thermalSandwichWeight hp₀ hq₀ hq₁ hpq).summable n

/-- The actual positive trace, obtained from the convergent diagonal series. -/
theorem positiveTrace_thermalSandwich {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) :
    positiveTrace (thermalSandwich p q τ) =
      ENNReal.ofReal (((1 - p) / (1 - q) ^ τ) / (1 - p / q ^ τ)) := by
  rw [thermalSandwich, positiveTrace_diagonalOperator numberBasis
    (hasSum_thermalSandwichWeight hp₀ hq₀ hq₁ hpq).summable
    (fun n => div_nonneg
      (mul_nonneg (sub_nonneg.mpr hp₁.le) (pow_nonneg hp₀ n))
      (Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ n) τ).le),
    (hasSum_thermalSandwichWeight hp₀ hq₀ hq₁ hpq).tsum_eq]

theorem thermalSandwich_isPositiveTraceClass {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) : IsPositiveTraceClass (thermalSandwich p q τ) := by
  refine ⟨thermalSandwich_nonneg hp₀ hp₁ hq₀ hq₁, ?_⟩
  rw [positiveTrace_thermalSandwich hp₀ hp₁ hq₀ hq₁ hpq]
  exact ENNReal.ofReal_lt_top

/-- The bounded extension is characterized by the genuine density
factorization, not by a totalized inverse. -/
theorem thermalSandwich_factorization {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ : 0 < τ) (hpq : p < q ^ τ) :
    (thermalDensity q ^ (τ / 2)) * thermalSandwich p q τ *
        (thermalDensity q ^ (τ / 2)) = thermalDensity p := by
  apply continuousLinearMap_eq_of_hilbertBasis numberBasis
  intro n
  have hhalf : 0 < τ / 2 := half_pos hτ
  have hwq : 0 < thermalWeight q n := thermalWeight_pos hq₀ hq₁ n
  have hpow : thermalWeight q n ^ (τ / 2) * thermalWeight q n ^ (τ / 2) =
      thermalWeight q n ^ τ := by
    rw [← Real.rpow_add hwq, add_halves]
  have hscalar : thermalWeight q n ^ (τ / 2) *
      thermalSandwichWeight p q τ n * thermalWeight q n ^ (τ / 2) = thermalWeight p n := by
    rw [thermalSandwichWeight]
    calc
      _ = (thermalWeight p n / thermalWeight q n ^ τ) *
          (thermalWeight q n ^ (τ / 2) * thermalWeight q n ^ (τ / 2)) := by ring
      _ = _ := by rw [hpow, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hwq τ))]
  simp only [mul_apply_eq_comp,
    thermalDensity_rpow_apply_numberBasis hq₀.le hq₁ hhalf,
    map_smul_of_tower, thermalSandwich_apply_numberBasis hp₀ hq₀ hq₁ hpq,
    thermalDensity_apply_numberBasis hp₀ hp₁, smul_smul]
  rw [hscalar]

/-- The quadratic form uses the actual inverse on its actual range domain. -/
noncomputable def thermalSandwichForm {p q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ)
    (x y : thermalPowerDomain q (τ / 2)) : ℂ :=
  inner ℂ (thermalInversePower hq₀ hq₁ (half_pos hτ) x)
    (thermalDensity p (thermalInversePower hq₀ hq₁ (half_pos hτ) y))

/-- The convergent-series operator extends the actual inverse-power form
on the dense domain. The target vectors retain their domain witnesses. -/
theorem thermalSandwichForm_eq_inner {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ : 0 < τ) (hpq : p < q ^ τ)
    (x y : thermalPowerDomain q (τ / 2)) :
    thermalSandwichForm (p := p) hq₀ hq₁ hτ x y =
      inner ℂ (x : OscillatorSpace) (thermalSandwich p q τ (y : OscillatorSpace)) := by
  let S := thermalDensity q ^ (τ / 2)
  let u := thermalInversePower hq₀ hq₁ (half_pos hτ) x
  let v := thermalInversePower hq₀ hq₁ (half_pos hτ) y
  have hS : IsSelfAdjoint S := CFC.rpow_nonneg.isSelfAdjoint
  have hx : S u = (x : OscillatorSpace) :=
    thermalPower_apply_inversePower hq₀ hq₁ (half_pos hτ) x
  have hy : S v = (y : OscillatorSpace) :=
    thermalPower_apply_inversePower hq₀ hq₁ (half_pos hτ) y
  change inner ℂ u (thermalDensity p v) = _
  calc
    _ = inner ℂ u (S (thermalSandwich p q τ (S v))) := by
      rw [← thermalSandwich_factorization hp₀ hp₁ hq₀ hq₁ hτ hpq]
      rfl
    _ = inner ℂ (S u) (thermalSandwich p q τ (S v)) := by
      simpa only [hS.adjoint_eq] using
        S.adjoint_inner_right u (thermalSandwich p q τ (S v))
    _ = _ := by rw [hx, hy]

/-- Injectivity and dense range of the positive half-power make the
bounded factorization unique. -/
theorem thermalSandwich_factorization_unique {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ : 0 < τ) (hpq : p < q ^ τ)
    {A : OscillatorSpace →L[ℂ] OscillatorSpace}
    (hA : (thermalDensity q ^ (τ / 2)) * A *
      (thermalDensity q ^ (τ / 2)) = thermalDensity p) :
    A = thermalSandwich p q τ := by
  let S := thermalDensity q ^ (τ / 2)
  have hS : Function.Injective S := thermalDensity_rpow_injective hq₀ hq₁ (half_pos hτ)
  have heq : S * A * S = S * thermalSandwich p q τ * S :=
    hA.trans (thermalSandwich_factorization hp₀ hp₁ hq₀ hq₁ hτ hpq).symm
  have hcomp : (fun z => A (S z)) = fun z => thermalSandwich p q τ (S z) := by
    funext z
    apply hS
    simpa only [mul_apply_eq_comp] using DFunLike.congr_fun heq z
  have hfun := (thermalDensity_rpow_denseRange hq₀ hq₁ (half_pos hτ)).equalizer
    A.continuous (thermalSandwich p q τ).continuous hcomp
  exact DFunLike.coe_injective hfun

end VacuumBellSeparation.Gaussian
