/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2AtomTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorArray
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# G2Moments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 3 of the `𝒢₂` lane: the `X_j` moment bound and `E[X_j^p] ≤ 1`

ABK26, §4.1, `e.Xj.moment.bound`:

```
E[X_j^p]^{1/p} ≤ C K₂ c⋆^{−2} s^{−4} ε^{−2} γ p  +  C K₂ s^{−5} ε^{−2} exp(−C^{−1}c⋆³γ^{−1}) p⁴ ,
```

the two summands being the images of the two Orlicz lanes of
`e.Xj.Orlicz.bound` under `e.moments.OGamma2` (`E[|X|^p]^{1/p} ≤ Cp^{1/σ}K`) at
`σ = 1` (giving the linear `p`) and `σ = 1/4` (giving `p⁴`); and then, at the
parameter choices `e.K.and.p.choices`, `E[X_j^p] ≤ 1`.

## Why the two lanes may not be merged

A `Γ_σ` tail implies a `Γ_{σ'}` tail at the same scale for `σ' ≤ σ`, so the
two-term display could be collapsed to a single `Γ_{1/4}` display.  That
collapse is *fatal here*: it replaces the linear `p` of the first term by `p⁴`,
and the manuscript's own verification of the first term — `C K₂ c⋆^{−2}s^{−4}
ε^{−2}γ·p =₂ K₁^{−1} ≤ 1/2` — depends on the exponent being exactly `1`.  This
is why the pair is never merged in the manuscript: no single
`σ` dominates both lanes.  The engine below therefore takes a genuine
two-term display and applies the ambient moment engine separately to each
witness, joining them with `ℝ≥0∞` Minkowski.

## The `E[X_j^p] ≤ 1` verification, faithfully

closes Step 3 with two numerical claims — "the first term equals `CK₂K₁^{−1} ≤ 1/2`
for `K₂K₁^{−1}` small" and "the second is `≤ 1/2` for `K₀` large enough".  Both
are *conditions on the proof-internal constants* `K₀,K₁,K₂` of
`e.K.and.p.choices`, which the lemma's proof is free to choose.  They are
carried here as the single explicit hypothesis `hnorm`

```
gammaMomentConst 1 · p · (Γ_1-scale)  +  gammaMomentConst (1/4) · p⁴ · (Γ_{1/4}-scale)  ≤  D ,
```

which is exactly the manuscript's sentence with the two halves added instead of
being bounded by `1/2` each.  No hypothesis is added that the manuscript does not
make, and no proof step migrates into a hypothesis: `hnorm` IS the manuscript's
constant-selection step.

## Scope

Provider material: proved local helpers.  `hcube` (the per-cube two-term
display, see `G2AtomTail`) and `hnorm` are conditional A obligations.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

/-! ## 1. Generic: scaling and the two-term moment engine -/

section Generic

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **Scaling of a two-term weak-Orlicz display.** -/
theorem isTwoTermBigOWith_const_mul {mu : Measure Omega} {Psi1 Psi2 : ℝ → ℝ}
    {X : Omega → ℝ} {A1 A2 c : ℝ} (hc : 0 < c)
    (h : Probability.IsTwoTermBigOWith mu Psi1 Psi2 X A1 A2) :
    Probability.IsTwoTermBigOWith mu Psi1 Psi2 (fun omega => c * X omega)
      (c * A1) (c * A2) := by
  obtain ⟨Y, Z, hP1, hP2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := h
  refine ⟨fun omega => c * Y omega, fun omega => c * Z omega, hP1, hP2,
    mul_pos hc hA1, mul_pos hc hA2, hXm.const_mul c, hYm.const_mul c, hZm.const_mul c,
    fun omega => ?_, hYt.const_mul hc.le, hZt.const_mul hc.le⟩
  calc c * X omega ≤ c * (Y omega + Z omega) :=
        mul_le_mul_of_nonneg_left (hdom omega) hc.le
    _ = c * Y omega + c * Z omega := by ring

/-- **`e.moments.OGamma2` at a two-term display (the Step-3 engine).**

For a nonnegative `X` with `X ≤ 𝒪_{Γ_{σ₁}}(A₁) + 𝒪_{Γ_{σ₂}}(A₂)` and `p ≥ 1`,

```
E[X^p]^{1/p} ≤ C(σ₁) p^{1/σ₁} A₁ + C(σ₂) p^{1/σ₂} A₂ .
```

The proof applies the ambient one-term moment engine to each clamped witness and
joins the two with `ℝ≥0∞` Minkowski; the statement is in the raised
`∫⁻ ≤ (…)^p` form the ambient engine and the Appendix-D interface both use. -/
theorem lintegral_rpow_le_of_twoTerm {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {sigma1 sigma2 A1 A2 p : ℝ}
    (hs1 : 0 < sigma1) (hs2 : 0 < sigma2) (hp : 1 ≤ p)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      X A1 A2) :
    ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu ≤
      ENNReal.ofReal ((gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
        gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) ^ p) := by
  obtain ⟨Y, Z, -, -, hA1, hA2, -, hYm, hZm, hdom, hYt, hZt⟩ := h
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set a : Omega → ℝ := fun omega => max (Y omega) 0 with ha
  set b : Omega → ℝ := fun omega => max (Z omega) 0 with hb
  have ha0 : ∀ omega, 0 ≤ a omega := fun _ => le_max_right _ _
  have hb0 : ∀ omega, 0 ≤ b omega := fun _ => le_max_right _ _
  have ham : Measurable a := hYm.max measurable_const
  have hbm : Measurable b := hZm.max measurable_const
  have hat : IsBigOWith mu (gammaSigma sigma1) a A1 := isBigOWith_max_zero hA1 hYt
  have hbt : IsBigOWith mu (gammaSigma sigma2) b A2 := isBigOWith_max_zero hA2 hZt
  set m1 : ℝ := gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 with hm1
  set m2 : ℝ := gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2 with hm2
  have hm10 : 0 ≤ m1 := by
    rw [hm1]
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos hs1).le (Real.rpow_nonneg hp0.le _)) hA1.le
  have hm20 : 0 ≤ m2 := by
    rw [hm2]
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos hs2).le (Real.rpow_nonneg hp0.le _)) hA2.le
  set f : Omega → ℝ≥0∞ := fun omega => ENNReal.ofReal (a omega) with hf
  set g : Omega → ℝ≥0∞ := fun omega => ENNReal.ofReal (b omega) with hg
  -- the pointwise domination, transported to `ℝ≥0∞`
  have hpt : ∀ omega, ENNReal.ofReal (X omega ^ p) ≤ (f + g) omega ^ p := by
    intro omega
    have hle : X omega ≤ a omega + b omega :=
      le_trans (hdom omega) (add_le_add (le_max_left _ _) (le_max_left _ _))
    calc ENNReal.ofReal (X omega ^ p)
        ≤ ENNReal.ofReal ((a omega + b omega) ^ p) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hX0 omega) hle hp0.le)
      _ = ENNReal.ofReal (a omega + b omega) ^ p :=
          (ENNReal.ofReal_rpow_of_nonneg (add_nonneg (ha0 omega) (hb0 omega)) hp0.le).symm
      _ = (f + g) omega ^ p := by
          rw [ENNReal.ofReal_add (ha0 omega) (hb0 omega)]
          rfl
  have hI : ∫⁻ omega, ENNReal.ofReal (X omega ^ p) ∂mu
      ≤ ∫⁻ omega, (f + g) omega ^ p ∂mu := lintegral_mono hpt
  -- the two one-term moment bounds
  have hlane : ∀ (c : Omega → ℝ) (sigma A : ℝ), 0 < sigma → 0 < A →
      (∀ omega, 0 ≤ c omega) → Measurable c →
      IsBigOWith mu (gammaSigma sigma) c A →
      (∫⁻ omega, ENNReal.ofReal (c omega) ^ p ∂mu) ^ (1 / p)
        ≤ ENNReal.ofReal (gammaMomentConst sigma * p ^ sigma⁻¹ * A) := by
    intro c sigma A hsigma hA hc0 hcm hct
    have hmom := lintegral_rpow_le_of_isBigOWith_gammaSigma hsigma hA hp hc0
      hcm.aemeasurable hct
    have hrw : ∫⁻ omega, ENNReal.ofReal (c omega) ^ p ∂mu
        = ∫⁻ omega, ENNReal.ofReal (c omega ^ p) ∂mu :=
      lintegral_congr fun omega =>
        ENNReal.ofReal_rpow_of_nonneg (hc0 omega) hp0.le
    have hM0 : 0 ≤ gammaMomentConst sigma * p ^ sigma⁻¹ * A :=
      mul_nonneg (mul_nonneg (gammaMomentConst_pos hsigma).le
        (Real.rpow_nonneg hp0.le _)) hA.le
    rw [hrw]
    refine le_trans (ENNReal.rpow_le_rpow hmom (by positivity)) ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg hM0 hp0.le, ← ENNReal.rpow_mul,
      mul_one_div_cancel (ne_of_gt hp0), ENNReal.rpow_one]
  have hstep1 := hlane a sigma1 A1 hs1 hA1 ha0 ham hat
  have hstep2 := hlane b sigma2 A2 hs2 hA2 hb0 hbm hbt
  have hmink := ENNReal.lintegral_Lp_add_le (μ := mu) (f := f) (g := g)
    ham.ennreal_ofReal.aemeasurable hbm.ennreal_ofReal.aemeasurable hp
  have hsum : (∫⁻ omega, (f + g) omega ^ p ∂mu) ^ (1 / p)
      ≤ ENNReal.ofReal (m1 + m2) := by
    refine le_trans hmink ?_
    rw [ENNReal.ofReal_add hm10 hm20]
    exact add_le_add hstep1 hstep2
  have hfinal : ∫⁻ omega, (f + g) omega ^ p ∂mu
      ≤ ENNReal.ofReal ((m1 + m2) ^ p) := by
    have hraise := ENNReal.rpow_le_rpow hsum hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hp0), ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (add_nonneg hm10 hm20) hp0.le] at hraise
    exact hraise
  exact le_trans hI hfinal

/-- **The Appendix-D unit moment from a two-term display.**  The normalized atom
`D^{-1}X` has `∫⁻ (D^{-1}X)^p ≤ 1` as soon as the two moment terms add up to at
most `D`.  This is the `hmomL` slot of the concentration interface, at the `𝒢₂`
lane's genuinely two-term display. -/
theorem lintegral_rpow_le_one_of_twoTerm {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {sigma1 sigma2 A1 A2 p D : ℝ}
    (hs1 : 0 < sigma1) (hs2 : 0 < sigma2) (hp : 1 ≤ p) (hD : 0 < D)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      X A1 A2)
    (hnorm : gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2 ≤ D) :
    ∫⁻ omega, ENNReal.ofReal ((D⁻¹ * X omega) ^ p) ∂mu ≤ 1 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hDinv : (0 : ℝ) < D⁻¹ := inv_pos.2 hD
  have hscaled := lintegral_rpow_le_of_twoTerm (X := fun omega => D⁻¹ * X omega)
    hs1 hs2 hp (fun omega => mul_nonneg hDinv.le (hX0 omega))
    (isTwoTermBigOWith_const_mul hDinv h)
  refine le_trans hscaled ?_
  have hbase : gammaMomentConst sigma1 * p ^ sigma1⁻¹ * (D⁻¹ * A1) +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * (D⁻¹ * A2)
      = D⁻¹ * (gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
        gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) := by ring
  rw [hbase]
  have hle1 : D⁻¹ * (gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) ≤ 1 := by
    calc D⁻¹ * (gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
          gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2)
        ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left hnorm hDinv.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hD)
  have hnn : 0 ≤ D⁻¹ * (gammaMomentConst sigma1 * p ^ sigma1⁻¹ * A1 +
      gammaMomentConst sigma2 * p ^ sigma2⁻¹ * A2) := by
    refine mul_nonneg hDinv.le (add_nonneg ?_ ?_)
    · exact mul_nonneg (mul_nonneg (gammaMomentConst_pos hs1).le
        (Real.rpow_nonneg hp0.le _)) (le_of_lt (by
          obtain ⟨_, _, _, _, hA1, -⟩ := h
          exact hA1))
    · exact mul_nonneg (mul_nonneg (gammaMomentConst_pos hs2).le
        (Real.rpow_nonneg hp0.le _)) (le_of_lt (by
          obtain ⟨_, _, _, _, _, hA2, -⟩ := h
          exact hA2))
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_one hnn hle1 hp0.le)) ?_
  simp

end Generic

/-! ## 2. The `𝒢₂` lane -/

variable {d : ℕ}

/-- The `Γ_1`-lane Orlicz scale of `X_j` produced by Step 2. -/
def xcalScaleOne (d : ℕ) (s A1 : ℝ) : ℝ :=
  gammaTriangleConst 1 *
    ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2))

/-- The `Γ_{1/4}`-lane Orlicz scale of `X_j` produced by Step 2; the
manuscript's `CK₂s^{−5}ε^{−2}exp(−C^{−1}c⋆³γ^{−1})`. -/
def xcalScaleQuarter (d : ℕ) (s A2 : ℝ) : ℝ :=
  gammaTriangleConst (1 / 4) *
    ∑' i : ℕ,
      weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))

/-- Step 2 in the packaged scale notation. -/
theorem isTwoTermBigOWith_Xcal_scales (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    {A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hcube : ∀ n : ℤ, n ≤ j - 1 →
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma (1 / 4)) (fun omega => (XcalE M s j omega).toReal)
      (xcalScaleOne d (s : ℝ) A1) (xcalScaleQuarter d (s : ℝ) A2) :=
  isTwoTermBigOWith_Xcal M s j hA1 hA2 hcube

/-- **The `𝒢₂` Appendix-D array**, `X_{k,j} = D^{-1}X_j`.  The normalizer `D`
carries the manuscript's `K₂ε^{−2}`. -/
def xcalArray (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ) :
    ℤ → ℤ → Cutoff.CutoffSample d → ℝ :=
  colArray fun j omega => D⁻¹ * (XcalE M s j omega).toReal

@[simp] theorem xcalArray_apply (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ)
    (k j : ℤ) (omega : Cutoff.CutoffSample d) :
    xcalArray M s D k j omega = D⁻¹ * (XcalE M s j omega).toReal := rfl

theorem measurable_xcalArray (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ)
    (k j : ℤ) : Measurable (xcalArray M s D k j) := by
  have heq : (fun omega : Cutoff.CutoffSample d => (XcalE M s j omega).toReal)
      = wsum (fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
        (fun i => weightThird ((s : ℝ) / 4) (i + 1)) := by
    funext omega
    rw [XcalE_eq_wsumE M s j omega]
    rfl
  have hbase : Measurable
      fun omega : Cutoff.CutoffSample d => (XcalE M s j omega).toReal := by
    rw [heq]
    exact measurable_wsum fun i => measurable_errorAnnMax M s j (j - 1 - (i : ℤ))
  exact hbase.const_mul D⁻¹

theorem xcalArray_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {D : ℝ} (hD : 0 < D)
    (k j : ℤ) (omega : Cutoff.CutoffSample d) : 0 ≤ xcalArray M s D k j omega :=
  mul_nonneg (inv_pos.2 hD).le ENNReal.toReal_nonneg

/-- **Step 3's conclusion `E[X_j^p] ≤ 1`, in the `∫⁻` reading, for the whole
Appendix-D array.**

`hnorm` is the manuscript's own constant-selection sentence — "for `K₂K₁^{−1}`
small" and "for `K₀` large enough" — with the two halves added rather than
bounded by `1/2` each.  `hcube` is the per-cube conditional A obligation of
`G2AtomTail`. -/
theorem lintegral_rpow_le_one_Xcal (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {A1 A2 p D : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (hp : 1 ≤ p) (hD : 0 < D)
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2)
    (hnorm : gammaMomentConst 1 * p * xcalScaleOne d (s : ℝ) A1 +
      gammaMomentConst (1 / 4) * p ^ (4 : ℝ) * xcalScaleQuarter d (s : ℝ) A2 ≤ D) :
    ∀ k j : ℤ, ∫⁻ omega, ENNReal.ofReal ((xcalArray M s D k j omega) ^ p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ 1 := by
  intro _k j
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have h1 : p ^ (1 : ℝ)⁻¹ = p := by rw [inv_one, Real.rpow_one]
  have h2 : p ^ ((1 : ℝ) / 4)⁻¹ = p ^ (4 : ℝ) := by norm_num
  refine lintegral_rpow_le_one_of_twoTerm (sigma1 := 1) (sigma2 := 1 / 4)
    (by norm_num) (by norm_num) hp hD (fun omega => ENNReal.toReal_nonneg)
    (isTwoTermBigOWith_Xcal_scales M s j hA1 hA2 (fun n _ => hcube n)) ?_
  rwa [h1, h2]

end

end Algsuperdiff.Section4.Provider.Proportion
