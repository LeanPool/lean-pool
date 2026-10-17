/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentSplitter

/-!
# MomentEngine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-term `Γ_σ`-tail → `q`-th-moment conversion, in the anchor's normal form

Nothing here imports that file, and nothing here claims the anchor.

## The target

Step 4 of the proof of `l.bounds.mathcal.E.aL` lists seven bullets and converts
four of them into moment bounds with the sentence "and hence, for every `q ∈
[1,∞)`", citing `l.moments.gamma.psi` (`E[|X|^q]^{1/q} ≤ C q^{1/σ} K`).  Three
of the four are ONE-term displays:

```
𝓔_{s,2,2}   (two-term; handled by `MomentSplitter`)
3^{2j}‖∇(k_L−k_{j−2})‖_{W^{1,∞}(□_j)}          ≤ 𝒪_{Γ₂}(C 3^{γ j})
‖k_L − k_{j−2} − (k_L−k_m)_{□_m}‖_{L²(□_j)}    ≤ 𝒪_{Γ₂}(C min{γ^{−1/2},(m−j)^{1/2}} 3^{γ m})
λ_{γ,2}^{-1}(□_j;𝐚_{j−2})                       ≤ C σ_{j−1}^{-1} + 𝒪_{Γ_{1/3}}(…)
```

and the remaining three bullets are D scalar inequalities, whose `q`-th moment
is the scalar itself (a probability measure has total mass one).

## Main results

* `lintegral_rpow_le_of_ae_le_const` — the deterministic bullets: an
  `ℝ≥0∞`-valued observable a.e. bounded by a constant has all its `q`-th
  moments bounded by that constant.
* `lintegral_rpow_le_of_isBigOWith_of_ae_le` — the one-term engine at general `σ`: an
  observable a.e. dominated by `ENNReal.ofReal ∘ X` with `X ≤ 𝒪_{Γ_σ}(A)` obeys `∫⁻ F^q ≤
  (.ofReal R)^q` for every real majorant `R` of `C(σ) q^{1/σ} A`.
* `lintegral_rpow_le_of_isBigOWith_gammaTwo`,
  `lintegral_ofReal_rpow_le_of_isBigOWith_gammaTwo` — the `σ = 2` instance,
  with `q^{1/σ}` evaluated to `Real.sqrt q` (the `√q` of the printed bullets,
  and the anchor's own `√p`).
* `lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le` — the shape of bullet
  (B5), whose display carries a D summand alongside the `Γ_{1/3}` one: `∫⁻ F^q
  ≤ (.ofReal R)^q` for every real majorant `R` of `b + C(σ) q^{1/σ} A`, by
  `ℝ≥0∞` Minkowski against the constant.
* `gammaMomentBound`, `gammaTwoMomentBound` — the majorants as named
  quantities, so a consumer can carry them symbolically.

## Route, and what is reused rather than re-proved

Nothing about it is re-derived here.  What is added is exactly what the
anchor's normal form needs and that engine does not have: the `ℝ≥0∞`-observable
left-hand side (so the literal, only-a.e.-measurable Step-4 objects can be the
subject via an a.e. domination), the `(.ofReal R) ^ q` right-hand side with a
caller-supplied majorant, and the evaluation of `q^{1/σ}` at `σ = 2`.  This is
the one-term twin of `MomentSplitter`, whose two-term statements have the same
shape and the same binders.

## Binders

Only the source binders: `1 ≤ q` (the range `q ∈ [1,∞)` of
`l.moments.gamma.psi`), `0 < σ`, positivity of the Orlicz scale (which the
two-term relation bundles and the one-term relation does not), nonnegativity
and a.e. measurability of the field, the display itself, the a.e. domination of
the observable, and the majorant inequality.  `IsProbabilityMeasure` is the
ambient hypothesis of `l.moments.gamma.psi`.

## References

* ABK26, `l.moments.gamma.psi`; `l.bounds.mathcal.E.aL`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. The one-term moment majorant -/

/-- The one-term moment majorant produced by `l.moments.gamma.psi`: `C(σ) q^{1/σ}
A`.  The constant is CoarseGraining's own `gammaMomentConst`, left in the
engine's normal form so that none is silently reshaped. -/
def gammaMomentBound (sigma p A : ℝ) : ℝ :=
  gammaMomentConst sigma * p ^ sigma⁻¹ * A

theorem gammaMomentBound_nonneg {sigma p A : ℝ} (hs : 0 < sigma) (hp : 0 ≤ p)
    (hA : 0 ≤ A) : 0 ≤ gammaMomentBound sigma p A := by
  have h1 : 0 ≤ gammaMomentConst sigma := (gammaMomentConst_pos hs).le
  have h2 : 0 ≤ p ^ sigma⁻¹ := Real.rpow_nonneg hp _
  unfold gammaMomentBound
  positivity

/-- The `σ = 2` moment majorant, with `q^{1/2}` spelled as `Real.sqrt q` — the
`√q` of the printed Step-4 bullets and the `√p` of the anchor's conclusion. -/
def gammaTwoMomentBound (p A : ℝ) : ℝ := gammaMomentConst 2 * Real.sqrt p * A

theorem gammaTwoMomentBound_eq (p A : ℝ) :
    gammaTwoMomentBound p A = gammaMomentBound 2 p A := by
  have he : ((2 : ℝ))⁻¹ = 1 / 2 := by norm_num
  unfold gammaTwoMomentBound gammaMomentBound
  rw [he, ← Real.sqrt_eq_rpow]

theorem gammaTwoMomentBound_nonneg {p A : ℝ} (hA : 0 ≤ A) :
    0 ≤ gammaTwoMomentBound p A := by
  have h1 : 0 ≤ gammaMomentConst 2 := (gammaMomentConst_pos (by norm_num)).le
  have h2 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  unfold gammaTwoMomentBound
  positivity

/-! ## 2. The deterministic bullets -/

/-! ## 3. The one-term Orlicz → moment splitter -/

/-- **The one-term `Γ_σ` → `lintegral` moment conversion**, in the normal form of
`bounds_mathcal_E_aL`.

If an `ℝ≥0∞`-valued observable `F` is almost surely dominated by `ENNReal.ofReal (X ·)`
for a nonnegative, a.e. measurable `X` carrying a display `X ≤ 𝒪_{Γ_σ}(A)`, then for every
`q ≥ 1` and every real `R` majorizing the engine's moment constant `C(σ) q^{1/σ} A`, `∫⁻
F^q ≤ (.ofReal R)^q`. -/
theorem lintegral_rpow_le_of_isBigOWith_of_ae_le {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {X : Omega → ℝ}
    {sigma A p R : ℝ} (hs : 0 < sigma) (hA : 0 < A) (hp : 1 ≤ p)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXm : AEMeasurable X mu)
    (h : IsBigOWith mu (gammaSigma sigma) X A)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ ENNReal.ofReal (X omega))
    (hR : gammaMomentBound sigma p A ≤ R) :
    ∫⁻ omega, F omega ^ p ∂mu ≤ ENNReal.ofReal R ^ p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hm0 : 0 ≤ gammaMomentBound sigma p A :=
    gammaMomentBound_nonneg hs hp0.le hA.le
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
      ENNReal.ofReal (gammaMomentBound sigma p A ^ p) :=
    lintegral_rpow_le_of_isBigOWith_gammaSigma hs hA hp hX0 hXm h
  have hstep4 : ENNReal.ofReal (gammaMomentBound sigma p A ^ p) ≤
      ENNReal.ofReal R ^ p := by
    rw [ENNReal.ofReal_rpow_of_nonneg hR0 hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hm0 hR hp0.le)
  calc ∫⁻ omega, F omega ^ p ∂mu
      ≤ ∫⁻ omega, ENNReal.ofReal (X omega) ^ p ∂mu := hstep1
    _ = ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu := hstep2
    _ ≤ ENNReal.ofReal (gammaMomentBound sigma p A ^ p) := hstep3
    _ ≤ ENNReal.ofReal R ^ p := hstep4

/-! ## 4. The `Γ₂` instance: the `√q` of the printed bullets -/

/-- **The `Γ₂` moment conversion.**  The `q^{1/σ}` of `l.moments.gamma.psi` at
`σ = 2` is `√q`, which is the `q^{1/2}` printed in the two `e.nabla.km.kn.infty`
bullets of Step 4 and the `√p` of the anchor's conclusion. -/
theorem lintegral_rpow_le_of_isBigOWith_gammaTwo {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {X : Omega → ℝ} {A p R : ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hX0 : ∀ omega, 0 ≤ X omega)
    (hXm : AEMeasurable X mu) (h : IsBigOWith mu (gammaSigma 2) X A)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ ENNReal.ofReal (X omega))
    (hR : gammaTwoMomentBound p A ≤ R) :
    ∫⁻ omega, F omega ^ p ∂mu ≤ ENNReal.ofReal R ^ p := by
  rw [gammaTwoMomentBound_eq] at hR
  exact lintegral_rpow_le_of_isBigOWith_of_ae_le (by norm_num) hA hp hX0 hXm h hF hR

/-- The `Γ₂` moment conversion with the observable taken to be `ENNReal.ofReal ∘ X`
itself. -/
theorem lintegral_ofReal_rpow_le_of_isBigOWith_gammaTwo {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A p R : ℝ} (hA : 0 < A)
    (hp : 1 ≤ p) (hX0 : ∀ omega, 0 ≤ X omega) (hXm : AEMeasurable X mu)
    (h : IsBigOWith mu (gammaSigma 2) X A) (hR : gammaTwoMomentBound p A ≤ R) :
    ∫⁻ omega, ENNReal.ofReal (X omega) ^ p ∂mu ≤ ENNReal.ofReal R ^ p :=
  lintegral_rpow_le_of_isBigOWith_gammaTwo hA hp hX0 hXm h
    (Filter.Eventually.of_forall fun _ => le_refl _) hR

/-! ## 5. The deterministic-shift shape: `b + 𝒪_{Γ_σ}(A)` -/

/-- **The moment conversion of a deterministically shifted one-term display.**

Bullet (B5) of Step 4 is the only bullet whose display has a D summand,
`λ_{γ,2}^{-1}(□_j;𝐚_{j−2}) ≤ C σ_{j−1}^{-1} + 𝒪_{Γ_{1/3}}(C
σ_{j−1}^{-1}exp(−C^{-1}γ^{-1}))`, and its printed moment conversion keeps the
two summands apart: `E[λ^{-q}]^{1/q} ≤ C σ_{j−1}^{-1}(1 + C q³
exp(−C^{-1}γ^{-1}))`.  The `q³` is `q^{1/σ}` at `σ = 1/3`.

The proof is `ℝ≥0∞` Minkowski against the constant, exactly as the manuscript's
`l.moments.gamma.psi` is applied to a sum. -/
theorem lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {X : Omega → ℝ}
    {sigma A b p R : ℝ} (hs : 0 < sigma) (hA : 0 < A) (hp : 1 ≤ p) (hb : 0 ≤ b)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXm : AEMeasurable X mu)
    (h : IsBigOWith mu (gammaSigma sigma) X A)
    (hF : ∀ᵐ omega ∂mu, F omega ≤ ENNReal.ofReal (b + X omega))
    (hR : b + gammaMomentBound sigma p A ≤ R) :
    ∫⁻ omega, F omega ^ p ∂mu ≤ ENNReal.ofReal R ^ p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hM0 : 0 ≤ gammaMomentBound sigma p A :=
    gammaMomentBound_nonneg hs hp0.le hA.le
  have hR0 : 0 ≤ R := le_trans (by linarith only [hb, hM0]) hR
  set f : Omega → ℝ≥0∞ := fun _ => ENNReal.ofReal b with hf
  set g : Omega → ℝ≥0∞ := fun omega => ENNReal.ofReal (X omega) with hg
  have hgm : AEMeasurable g mu := hXm.ennreal_ofReal
  have hstep1 : ∫⁻ omega, F omega ^ p ∂mu ≤ ∫⁻ omega, (f + g) omega ^ p ∂mu := by
    refine lintegral_mono_ae ?_
    filter_upwards [hF] with omega homega
    refine ENNReal.rpow_le_rpow (le_trans homega (le_of_eq ?_)) hp0.le
    rw [ENNReal.ofReal_add hb (hX0 omega)]
    rfl
  have hmink : (∫⁻ omega, (f + g) omega ^ p ∂mu) ^ (1 / p) ≤
      (∫⁻ omega, f omega ^ p ∂mu) ^ (1 / p) +
        (∫⁻ omega, g omega ^ p ∂mu) ^ (1 / p) :=
    ENNReal.lintegral_Lp_add_le (μ := mu) (f := f) (g := g)
      measurable_const.aemeasurable hgm hp
  have hconst : (∫⁻ omega, f omega ^ p ∂mu) ^ (1 / p) = ENNReal.ofReal b := by
    rw [hf, lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
      mul_one_div_cancel (ne_of_gt hp0), ENNReal.rpow_one]
  have hgbound : ∫⁻ omega, g omega ^ p ∂mu ≤
      ENNReal.ofReal (gammaMomentBound sigma p A) ^ p :=
    lintegral_rpow_le_of_isBigOWith_of_ae_le hs hA hp hX0 hXm h
      (Filter.Eventually.of_forall fun _ => le_refl _) le_rfl
  have hgroot : (∫⁻ omega, g omega ^ p ∂mu) ^ (1 / p) ≤
      ENNReal.ofReal (gammaMomentBound sigma p A) := by
    refine le_trans (ENNReal.rpow_le_rpow hgbound (by positivity)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hp0), ENNReal.rpow_one]
  have hsum : (∫⁻ omega, (f + g) omega ^ p ∂mu) ^ (1 / p) ≤ ENNReal.ofReal R := by
    refine le_trans hmink ?_
    refine le_trans (add_le_add (le_of_eq hconst) hgroot) ?_
    rw [← ENNReal.ofReal_add hb hM0]
    exact ENNReal.ofReal_le_ofReal hR
  have hraise := ENNReal.rpow_le_rpow hsum hp0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hp0), ENNReal.rpow_one] at hraise
  exact le_trans hstep1 hraise

end

end Algsuperdiff.Section4.Provider.BoundsEaL
