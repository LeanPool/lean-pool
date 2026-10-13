/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Concentration

/-!
# ProductPower

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Multiplication and power rules for stretched-exponential tails

This module pins the ABK26 Appendix multiplication lemma and its power-rule
corollary in the exact shape used by the Section 3 call sites.

Both statements are already available in CoarseGraining:

* the multiplication property is
  `Homogenization.Book.Ch04.isBigOWith_gammaSigma_mul`;
* the power rule is
  `Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow_iff`.

The declarations below are therefore bindings rather than new proofs, except
for the natural-exponent square specialization, which converts the real power
`X ^ (2 : ℝ)` of the CoarseGraining statement into the monoid power `X ^ (2:
ℕ)` that downstream consumers write.

## Main results

* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_mul_of_nonneg`
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg`
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg`

## References

* ABK26, Lemma `l.o.gamma2.mult`, equations `e.multGammasig` and
  `e.powerofGammasigma`.
* ABK26, Appendix.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Multiplication property for nonnegative random variables with
stretched-exponential upper tails: the product has a `Γ_τ` tail with
`τ = σ₁ σ₂ / (σ₁ + σ₂)`.

This is a binding of `Homogenization.Book.Ch04.isBigOWith_gammaSigma_mul`.  The
scale carries CoarseGraining's explicit factor
`Homogenization.Book.Ch04.gammaProductConst σ₁ σ₂ = 2 ^ τ⁻¹`, with `τ = σ₁ σ₂ /
(σ₁ + σ₂)`.

The standard threshold split produces two bad events, so `P[X Y > A B t] ≤ 2
exp (-t ^ τ)`; at `t = 1` two disjoint near-saturating tail events push the
product event to nearly `2 e⁻¹ > e⁻¹`, so no constant-free statement can hold.
CoarseGraining's `gammaProductConst σ₁ σ₂ = 2 ^ (1 / τ)` is larger than that
minimum, hence also valid, and is the constant carried by this binding. -/
theorem isBigOWith_gammaSigma_mul_of_nonneg [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} {A B σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hX : IsBigOWith μ (gammaSigma σ₁) X A)
    (hY : IsBigOWith μ (gammaSigma σ₂) Y B) :
    IsBigOWith μ (gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂))) (fun ω => X ω * Y ω)
      (HCPolySupport.Book.Ch04.gammaProductConst σ₁ σ₂ * A * B) :=
  HCPolySupport.Book.Ch04.isBigOWith_gammaSigma_mul hσ₁ hσ₂ hA hB
    hX_nonneg hY_nonneg hX hY

/-- Power rule for nonnegative random variables:
`X ≤ O_{Γ_σ}(K) ↔ X ^ p ≤ O_{Γ_{σ/p}}(K ^ p)`, with real exponent `p > 0`.

This is a binding of
`Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow_iff` and matches
`e.powerofGammasigma` with no loss of constant. -/
theorem isBigOWith_gammaSigma_rpow_iff_of_nonneg [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K σ p : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    IsBigOWith μ (gammaSigma σ) X K ↔
      IsBigOWith μ (gammaSigma (σ / p)) (fun ω => X ω ^ p) (K ^ p) :=
  isBigOWith_gammaSigma_rpow_iff hp hK hX_nonneg

/-- The square specialization of the power rule, with the natural-number
exponent used by downstream consumers. -/
theorem isBigOWith_gammaSigma_sq_iff_of_nonneg [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K σ : ℝ}
    (hK : 0 ≤ K) (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    IsBigOWith μ (gammaSigma σ) X K ↔
      IsBigOWith μ (gammaSigma (σ / 2)) (fun ω => X ω ^ 2) (K ^ 2) := by
  have h := isBigOWith_gammaSigma_rpow_iff (μ := μ) (X := X) (A := K) (σ := σ)
    (p := 2) (by norm_num) hK hX_nonneg
  simpa only [Real.rpow_two] using h

end

end Algsuperdiff.Section3.Provider.Orlicz
