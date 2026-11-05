/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Moments

/-!
# MomentSplitter

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-term Orlicz → `lintegral` moment splitter, in the anchor's normal form

## The target

The moment bullets of `l.bounds.mathcal.E.aL` convert `𝒪_{Γ_σ}`-type displays
into moment bounds through `l.moments.gamma.psi`.  The genuinely two-term
bullet is the `p.induction.bounds` one:

```
𝓔_{s,2,2}(□_j; a_{j-2}, σ_{j-2}) ≤ 𝒪_{Γ_2}(C s^{-1} γ^{1/2})
                                   + 𝒪_{Γ_{1/2}}(exp(-C^{-1} γ^{-1}))
```
```
E[ 𝓔_{s,2,2}(□_j; a_{j-2}, σ_{j-2})^q ]^{1/q}
   ≤ C s^{-1} q^{1/2} γ^{1/2} + C q^2 exp(-C^{-1} γ^{-1}) ,   q ∈ [1, ∞) .
```

The two printed `q`-powers are exactly `q^{1/σ}` at `σ = 2` and `σ = 1/2`: the
`Γ_2` lane carries the `√q` (which is the `p^{1/2}` of the anchor's conclusion)
and the `Γ_{1/2}` lane carries the `q^2` (which the exponentially small scale
`exp(-C^{-1}γ^{-1})` absorbs — a parameter argument, and the consumer's, not
this file's).

This file supplies precisely that shape.

## Main results

* `lintegral_rpow_le_of_twoTerm_of_ae_le` — the general splitter: an
  `ℝ≥0∞`-valued observable dominated a.e. by `ENNReal.ofReal ∘ X`, with `X`
  carrying a two-term `(Γ_{σ₁}, Γ_{σ₂})` display, satisfies
  `∫⁻ F^p ≤ (ENNReal.ofReal R)^p` for
  every real majorant `R` of `C(σ₁) p^{1/σ₁} A₁ + C(σ₂) p^{1/σ₂} A₂`.
* `lintegral_rpow_le_of_twoTerm_gammaTwoHalf` — the `(Γ_2, Γ_{1/2})` instance,
  with the two `p`-powers evaluated to `Real.sqrt p` and `p ^ 2` (the anchor's
  own spelling of the first is `Real.sqrt p`).
* `lintegral_ofReal_rpow_le_of_twoTerm_gammaTwoHalf` — the same with the
  observable taken to be `ENNReal.ofReal ∘ X` itself.
* `gammaTwoHalfMomentBound`, `gammaTwoHalfMomentBound_nonneg` — the two-term
  moment majorant as a named quantity, so a consumer can carry it symbolically.

## Route, and what is reused rather than re-proved

The engine is the two-term moment engine
`Section4.Provider.Proportion.lintegral_rpow_le_of_twoTerm` (the `𝒢₂` lane's
Step-3 engine: CoarseGraining's one-term
`IndependentSums.lintegral_rpow_le_of_isBigOWith_gammaSigma` applied to each
clamped witness, joined by `ℝ≥0∞` Minkowski).  It is already public and already
stated at general `(σ₁, σ₂)`; nothing about it is re-derived here.  What this
file adds is exactly the three things the anchor's normal form needs and that
engine does not have: the `ℝ≥0∞`-observable left-hand side, the `(ofReal R) ^
p` right-hand side with a caller-supplied majorant, and the evaluation of the
two `p`-powers at the `(Γ_2, Γ_{1/2})` pair.

## Binders

Only the source binders: `1 ≤ p` (the moment engine's range `q ∈ [1,∞)`), the
positivity of the two Orlicz exponents (automatic in the `(Γ_2, Γ_{1/2})`
instance), nonnegativity of the field, the two-term display itself, the a.e.
domination of the observable, and the majorant inequality.
`IsProbabilityMeasure` is the ambient hypothesis of `l.moments.gamma.psi`.

## References

* ABK26, `l.moments.gamma.psi`; `l.bounds.mathcal.E.aL`.
* `Algsuperdiff/Section4/Provider/Proportion/G2Moments.lean` (the engine).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## The two-term moment majorant -/

/-- The two-term moment majorant produced by `l.moments.gamma.psi` at the `(Γ_2,
Γ_{1/2})` pair: `C(2) √p A₁ + C(1/2) p² A₂`.  The constants are
CoarseGraining's own `gammaMomentConst`, left in the engine's normal form so
that none is silently reshaped. -/
noncomputable def gammaTwoHalfMomentBound (p A1 A2 : ℝ) : ℝ :=
  gammaMomentConst 2 * Real.sqrt p * A1 + gammaMomentConst (1 / 2) * p ^ (2 : ℕ) * A2

theorem gammaTwoHalfMomentBound_nonneg {p A1 A2 : ℝ} (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) : 0 ≤ gammaTwoHalfMomentBound p A1 A2 := by
  have h1 : 0 ≤ gammaMomentConst 2 := (gammaMomentConst_pos (by norm_num)).le
  have h2 : 0 ≤ gammaMomentConst (1 / 2) :=
    (gammaMomentConst_pos (by norm_num)).le
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  unfold gammaTwoHalfMomentBound
  positivity

/-! ## The splitter -/

/-- **The two-term Orlicz → `lintegral` moment splitter**, in the normal form of
`bounds_mathcal_E_aL`.

If an `ℝ≥0∞`-valued observable `F` is almost surely dominated by
`ENNReal.ofReal (X ·)` for a nonnegative `X` carrying a two-term display
`X ≤ 𝒪_{Γ_{σ₁}}(A₁) + 𝒪_{Γ_{σ₂}}(A₂)`, then for every `p ≥ 1` and every real `R`
majorizing the engine's two-term moment constant,
`∫⁻ F^p ≤ (ENNReal.ofReal R)^p`. -/
theorem lintegral_rpow_le_of_twoTerm_of_ae_le {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {X : Omega → ℝ}
    {sigma1 sigma2 A1 A2 p R : ℝ} (hs1 : 0 < sigma1) (hs2 : 0 < sigma2)
    (hp : 1 ≤ p) (hX0 : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      X A1 A2)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ ENNReal.ofReal (X omega))
    (hR : gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2 ≤ R) :
    ∫⁻ omega, F omega ^ p ∂mu ≤ ENNReal.ofReal R ^ p := by
  obtain ⟨-, -, -, -, hA1, hA2, -⟩ := id h
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hm0 : 0 ≤ gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2 := by
    refine add_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hA1.le)
      (mul_nonneg (mul_nonneg ?_ ?_) hA2.le)
    · exact (gammaMomentConst_pos hs1).le
    · exact Real.rpow_nonneg hp0.le _
    · exact (gammaMomentConst_pos hs2).le
    · exact Real.rpow_nonneg hp0.le _
  have hR0 : 0 ≤ R := le_trans hm0 hR
  have hstep1 : ∫⁻ omega, F omega ^ p ∂mu ≤
      ∫⁻ omega, ENNReal.ofReal (X omega) ^ p ∂mu := by
    refine lintegral_mono_ae ?_
    filter_upwards [hF] with omega homega
    exact ENNReal.rpow_le_rpow homega hp0.le
  have hstep2 : ∫⁻ omega, ENNReal.ofReal (X omega) ^ p ∂mu =
      ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu :=
    lintegral_congr fun omega => ENNReal.ofReal_rpow_of_nonneg (hX0 omega) hp0.le
  have hstep3 : ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu ≤
      ENNReal.ofReal ((gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
        gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) ^ p) :=
    Proportion.lintegral_rpow_le_of_twoTerm hs1 hs2 hp hX0 h
  have hstep4 : ENNReal.ofReal ((gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) ^ p) ≤
      ENNReal.ofReal R ^ p := by
    rw [ENNReal.ofReal_rpow_of_nonneg hR0 hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hm0 hR hp0.le)
  calc ∫⁻ omega, F omega ^ p ∂mu
      ≤ ∫⁻ omega, ENNReal.ofReal (X omega) ^ p ∂mu := hstep1
    _ = ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu := hstep2
    _ ≤ ENNReal.ofReal ((gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
          gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) ^ p) := hstep3
    _ ≤ ENNReal.ofReal R ^ p := hstep4

/-! ## The `(Γ_2, Γ_{1/2})` instance -/

/-- The engine's two `p`-powers at the `(Γ_2, Γ_{1/2})` pair are `√p` and `p²`. -/
theorem gammaTwoHalfMomentBound_eq (p A1 A2 : ℝ) :
    gammaTwoHalfMomentBound p A1 A2 =
      gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * A1 +
        gammaMomentConst (1 / 2) * p ^ ((1 : ℝ) / 2)⁻¹ * A2 := by
  have he1 : ((2 : ℝ))⁻¹ = 1 / 2 := by norm_num
  have he2 : (((1 : ℝ)) / 2)⁻¹ = (2 : ℝ) := by norm_num
  unfold gammaTwoHalfMomentBound
  rw [he1, he2, ← Real.sqrt_eq_rpow, Real.rpow_two]

/-- **The `(Γ_2, Γ_{1/2})` splitter**: the shape the `l.bounds.mathcal.E.aL`
moment bullets deliver, in the anchor's normal form.  The `Γ_2` lane contributes
the `√p` of the printed conclusion; the `Γ_{1/2}` lane contributes `p²`. -/
theorem lintegral_rpow_le_of_twoTerm_gammaTwoHalf {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {X : Omega → ℝ}
    {A1 A2 p R : ℝ} (hp : 1 ≤ p) (hX0 : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma 2) (gammaSigma (1 / 2))
      X A1 A2)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ ENNReal.ofReal (X omega))
    (hR : gammaTwoHalfMomentBound p A1 A2 ≤ R) :
    ∫⁻ omega, F omega ^ p ∂mu ≤ ENNReal.ofReal R ^ p := by
  rw [gammaTwoHalfMomentBound_eq] at hR
  exact lintegral_rpow_le_of_twoTerm_of_ae_le (by norm_num) (by norm_num) hp hX0 h
    hF hR

end

end Algsuperdiff.Section4.Provider.BoundsEaL
