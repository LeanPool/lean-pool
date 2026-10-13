/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Score
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# G2AtomTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` tail lane: Step 1 (the squared annular maximum) and Step 2 (`X_j`)

ABK26, §4.1, `e.mathcalE.squared.max.bound` and `e.Xj.Orlicz.bound`.

```
max_{z ∈ 3^nℤ^d ∩ (□_j∖□_{j−1})} 𝓔_{s,2,2}(z+□_n;𝐚_{n−2},σ_{n−2})²
   ≤ 𝒪_{Γ_1}( C(j−n+1) c⋆^{−2}s^{−2}γ ) + 𝒪_{Γ_{1/4}}( C(j−n+1)⁴ exp(−C^{−1}c⋆³γ^{−1}) ) ,

X_j = K₂ε^{−2} Σ_{n ≤ j−1} 3^{−¼s(j−n)} (that maximum)
   ≤ 𝒪_{Γ_1}( CK₂c⋆^{−2}s^{−4}ε^{−2}γ ) + 𝒪_{Γ_{1/4}}( CK₂s^{−5}ε^{−2}exp(−C^{−1}c⋆³γ^{−1}) ) .
```

## What is derived, and from what

The manuscript's Step 1 cites four inputs.  Three of them are *performed* here:

* `e.powerofGammasigma` — squaring moves the Orlicz indices `(2, 1/2)` to `(1,
  1/4)` and squares the amplitudes.
* `e.maxy.bound` — the union bound over the annulus centres.
* the lattice centre `z` — stationarity, not a new estimate: the per-cube atom
  at `z` is the origin atom read at the translated sample, and
  `AtomTail.isBigOWith_comp_measurePreserving` transports the tail at every
  real `z`.  No per-`z` instance of any Section 3 statement is used.

The fourth input, `Proposition p.induction.bounds` composed with "subadditivity
of `𝓔`", is **NOT** derived here and is carried as the explicit hypothesis
`hcube` of `isTwoTermBigOWith_errorAnnMax`.  See the Frontier note below.

Step 2 is the *two-term* countable generalized triangle inequality
`isTwoTermBigOWith_wsum`, proved here.  The `𝒢₀` lane's one-term device
(`SeriesTail.isBigOWith_wsum`) does not suffice: the two Orlicz indices are
never merged in the manuscript, and merging them at `σ = 1/4` would replace the
linear `p` of Step 3's first term by `p⁴` and break the verification `E[X_j^p]
≤ 1`.  The device splits each summand, `T = min(Y⁺, T) + (T − min(Y⁺, T))`, so
that the two `ℝ≥0∞` series add up to the original one on the nose and the
`.toReal` domination holds *everywhere*, including at the sample points where a
series diverges.

## Frontier (declared, not smuggled)

`hcube` is the display

```
𝓔_{s,2,2}(□_n; 𝐚_{n−2}, σ_{n−2}) ≤ 𝒪_{Γ_2}(A₁) + 𝒪_{Γ_{1/2}}(A₂)
```

at the O cube.  The Section 3 anchor `p.induction.bounds`
(`Frozen.Section3.induction_bounds`) supplies exactly this shape, but at the
DIAGONAL triple (coefficient scale, domain scale, comparator scale) `= (m,m,m)`
and at the exponent pair `(∞,2)`; the `𝒢₂` atom needs `(n−2, n, n−2)` at
`(2,2)`.  It is therefore taken as a hypothesis, not improvised.  Note that the
standing regime `γ ≤ C^{−10}c⋆^{10}` needed to instantiate the anchor is, per
the graph, discharged at the caller and does not appear here at all.

## Scope

Provider material: proved local helpers.  `hcube` is a conditional A
obligation, not a source premise.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

/-! ## 1. Two elementary devices -/

section Generic

variable {Omega : Type*} [MeasurableSpace Omega]

variable {iota : Type*}

/-- **A `0`-floored maximum of a pointwise sum splits.**  No sign condition on
the summands is needed: the `0`-floor of the right side does the work. -/
theorem fmax_le_add_fmax (S : Finset iota) (T Y Z : iota → ℝ)
    (h : ∀ i ∈ S, T i ≤ Y i + Z i) :
    fmax S T ≤ fmax S Y + fmax S Z :=
  fmax_le (add_nonneg (fmax_nonneg _ _) (fmax_nonneg _ _)) fun i hi =>
    le_trans (h i hi) (add_le_add (le_fmax hi) (le_fmax hi))

/-- `(a+b)² ≤ 2a² + 2b²`, the elementary inequality that turns a two-term
`𝒪_{Γ}`-display into a two-term display for the square. -/
theorem sq_add_le_two_mul (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := sq_nonneg (a - b)
  have hexp : (a - b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 - (a + b) ^ 2 := by ring
  linarith only [h, hexp]

end Generic

/-! ## 2. The two-term countable generalized triangle inequality -/

section TwoTermSeries

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The `Γ_{σ₁}`-half of the exact splitting of a nonnegative atom. -/
def splitLow (T Y : Omega → ℝ) (omega : Omega) : ℝ :=
  min (max (Y omega) 0) (T omega)

/-- The `Γ_{σ₂}`-half; by construction `T = splitLow + splitHigh` exactly. -/
def splitHigh (T Y : Omega → ℝ) (omega : Omega) : ℝ :=
  T omega - splitLow T Y omega

omit [MeasurableSpace Omega] in
private theorem splitLow_nonneg {T Y : Omega → ℝ} (hT : ∀ omega, 0 ≤ T omega)
    (omega : Omega) : 0 ≤ splitLow T Y omega :=
  le_min (le_max_right _ _) (hT omega)

omit [MeasurableSpace Omega] in
private theorem splitLow_le_max {T Y : Omega → ℝ} (omega : Omega) :
    splitLow T Y omega ≤ max (Y omega) 0 := min_le_left _ _

omit [MeasurableSpace Omega] in
private theorem splitLow_le {T Y : Omega → ℝ} (omega : Omega) :
    splitLow T Y omega ≤ T omega := min_le_right _ _

omit [MeasurableSpace Omega] in
private theorem splitHigh_nonneg {T Y : Omega → ℝ} (omega : Omega) :
    0 ≤ splitHigh T Y omega := by
  have := splitLow_le (T := T) (Y := Y) omega
  simp only [splitHigh]
  linarith only [this]

omit [MeasurableSpace Omega] in
private theorem splitHigh_le_max {T Y Z : Omega → ℝ}
    (hdom : ∀ omega, T omega ≤ Y omega + Z omega) (omega : Omega) :
    splitHigh T Y omega ≤ max (Z omega) 0 := by
  have hstep : T omega ≤ max (Y omega) 0 + max (Z omega) 0 :=
    le_trans (hdom omega) (add_le_add (le_max_left _ _) (le_max_left _ _))
  simp only [splitHigh, splitLow]
  rcases le_total (max (Y omega) 0) (T omega) with h | h
  · rw [min_eq_left h]
    linarith only [hstep]
  · rw [min_eq_right h]
    have : (0 : ℝ) ≤ max (Z omega) 0 := le_max_right _ _
    linarith only [this]

omit [MeasurableSpace Omega] in
private theorem splitLow_add_splitHigh {T Y : Omega → ℝ} (omega : Omega) :
    splitLow T Y omega + splitHigh T Y omega = T omega := by
  simp only [splitHigh]
  ring

private theorem measurable_splitLow {T Y : Omega → ℝ} (hT : Measurable T)
    (hY : Measurable Y) : Measurable (splitLow T Y) :=
  (hY.max measurable_const).min hT

private theorem measurable_splitHigh {T Y : Omega → ℝ} (hT : Measurable T)
    (hY : Measurable Y) : Measurable (splitHigh T Y) :=
  hT.sub (measurable_splitLow hT hY)

omit [MeasurableSpace Omega] in
/-- **The weighted `ℝ≥0∞` series of an exact splitting splits.** -/
private theorem wsumE_add {T U V : ℕ → Omega → ℝ} {c : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hU : ∀ i omega, 0 ≤ U i omega)
    (hV : ∀ i omega, 0 ≤ V i omega)
    (hsplit : ∀ i omega, U i omega + V i omega = T i omega) (omega : Omega) :
    wsumE T c omega = wsumE U c omega + wsumE V c omega := by
  rw [wsumE, wsumE, wsumE, ← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (hc i) (hU i omega))
    (mul_nonneg (hc i) (hV i omega)), ← mul_add, hsplit i omega]

omit [MeasurableSpace Omega] in
/-- **The real weighted series of an exact splitting is dominated everywhere.**
At the sample points where the series diverges the left side is `0` by the
`.toReal` convention, so no `a.s.` qualifier and no finiteness hypothesis is
needed. -/
private theorem wsum_le_add {T U V : ℕ → Omega → ℝ} {c : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hU : ∀ i omega, 0 ≤ U i omega)
    (hV : ∀ i omega, 0 ≤ V i omega)
    (hsplit : ∀ i omega, U i omega + V i omega = T i omega) (omega : Omega) :
    wsum T c omega ≤ wsum U c omega + wsum V c omega := by
  have hE := wsumE_add hc hU hV hsplit omega
  rcases eq_or_ne (wsumE T c omega) (⊤ : ℝ≥0∞) with htop | htop
  · have h0 : wsum T c omega = 0 := by
      rw [wsum, htop, ENNReal.toReal_top]
    rw [h0]
    exact add_nonneg (wsum_nonneg _ _ _) (wsum_nonneg _ _ _)
  · have hUne : wsumE U c omega ≠ (⊤ : ℝ≥0∞) := by
      intro hcon
      rw [hE, hcon] at htop
      exact htop (by simp)
    have hVne : wsumE V c omega ≠ (⊤ : ℝ≥0∞) := by
      intro hcon
      rw [hE, hcon] at htop
      exact htop (by simp)
    rw [wsum, wsum, wsum, hE, ENNReal.toReal_add hUne hVne]

/-- **The two-term countable generalized triangle inequality
(`e.Gamma.sigma.triangle`, both lanes at once).**

For nonnegative measurable atoms `T_i` with a two-term weak-Orlicz display at
per-summand scales `a₁ i, a₂ i`, positive weights `c_i`, and both weighted scale
series summable, the total `ℝ≥0∞` series `wsum T c` has a two-term display at the
scales `gammaTriangleConst σ_k · Σ_i c_i a_k i`.

This is the device Step 2 needs and the ambient library does not have: the
library's `Γ_σ` triangle inequality is one-term, and applying it twice is not
possible because the two witnesses of a two-term display are not themselves
series of the summands' witnesses.  The exact splitting `splitLow/splitHigh`
removes that obstruction. -/
theorem isTwoTermBigOWith_wsum {mu : Measure Omega} [IsFiniteMeasure mu]
    {T : ℕ → Omega → ℝ} {c a1 a2 : ℕ → ℝ} {sigma1 sigma2 : ℝ}
    (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2)
    (hT0 : ∀ i omega, 0 ≤ T i omega) (hTm : ∀ i, Measurable (T i))
    (hc : ∀ i, 0 < c i) (ha1 : ∀ i, 0 < a1 i) (ha2 : ∀ i, 0 < a2 i)
    (hsum1 : Summable fun i => c i * a1 i) (hsum2 : Summable fun i => c i * a2 i)
    (hT : ∀ i, Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      (T i) (a1 i) (a2 i)) :
    Probability.IsTwoTermBigOWith mu (gammaSigma sigma1) (gammaSigma sigma2)
      (wsum T c)
      (gammaTriangleConst sigma1 * ∑' i : ℕ, c i * a1 i)
      (gammaTriangleConst sigma2 * ∑' i : ℕ, c i * a2 i) := by
  classical
  choose Y Z hW using hT
  set U : ℕ → Omega → ℝ := fun i => splitLow (T i) (Y i) with hU
  set V : ℕ → Omega → ℝ := fun i => splitHigh (T i) (Y i) with hV
  have hU0 : ∀ i omega, 0 ≤ U i omega := fun i => splitLow_nonneg (fun o => hT0 i o)
  have hV0 : ∀ i omega, 0 ≤ V i omega := fun i _ => splitHigh_nonneg _
  have hsplit : ∀ i omega, U i omega + V i omega = T i omega := fun i =>
    splitLow_add_splitHigh
  have hUm : ∀ i, Measurable (U i) := fun i =>
    measurable_splitLow (hTm i) (hW i).2.2.2.2.2.1
  have hVm : ∀ i, Measurable (V i) := fun i =>
    measurable_splitHigh (hTm i) (hW i).2.2.2.2.2.1
  -- the per-summand tails of the two halves
  have hUtail : ∀ i, IsBigOWith mu (gammaSigma sigma1) (U i) (a1 i) := by
    intro i
    refine IsBigOWith.of_le ?_ (fun omega => splitLow_le_max omega)
    exact isBigOWith_max_zero (ha1 i) (hW i).2.2.2.2.2.2.2.2.1
  have hVtail : ∀ i, IsBigOWith mu (gammaSigma sigma2) (V i) (a2 i) := by
    intro i
    refine IsBigOWith.of_le ?_ (fun omega => splitHigh_le_max (hW i).2.2.2.2.2.2.2.1 omega)
    exact isBigOWith_max_zero (ha2 i) (hW i).2.2.2.2.2.2.2.2.2
  -- the series tails
  have hUsum := isBigOWith_wsum hsigma1 hU0 hUm hc ha1 hsum1 hUtail
  have hVsum := isBigOWith_wsum hsigma2 hV0 hVm hc ha2 hsum2 hVtail
  have hS1 : 0 < ∑' i : ℕ, c i * a1 i :=
    hsum1.tsum_pos (fun i => (mul_pos (hc i) (ha1 i)).le) 0 (mul_pos (hc 0) (ha1 0))
  have hS2 : 0 < ∑' i : ℕ, c i * a2 i :=
    hsum2.tsum_pos (fun i => (mul_pos (hc i) (ha2 i)).le) 0 (mul_pos (hc 0) (ha2 0))
  refine Provider.Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma hsigma1)
    (Probability.isAdmissibleTail_gammaSigma hsigma2)
    (mul_pos (gammaTriangleConst_pos (σ := sigma1)) hS1)
    (mul_pos (gammaTriangleConst_pos (σ := sigma2)) hS2)
    (measurable_wsum hTm) (measurable_wsum hUm) (measurable_wsum hVm)
    (Filter.Eventually.of_forall fun omega =>
      wsum_le_add (fun i => (hc i).le) hU0 hV0 hsplit omega)
    hUsum hVsum

end TwoTermSeries

/-! ## 3. Step 1 — the squared annular maximum -/

variable {d : ℕ}

/-- **Step 1, `e.mathcalE.squared.max.bound`.**

`hcube` is the conditional A obligation described in the module docstring; the
lattice translation and the squaring are performed here. -/
theorem isTwoTermBigOWith_errorAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {A1 A2 : ℝ} (j n : ℤ)
    (hcube : Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s) A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma (1 / 4)) (errorAnnMax M s j n)
      (annulusPenalty d 1 (j - n).toNat * (2 * A1 ^ 2))
      (annulusPenalty d (1 / 4) (j - n).toNat * (2 * A2 ^ 2)) := by
  classical
  obtain ⟨Y, Z, -, -, hA1, hA2, hEm, hYm, hZm, hdom, hYt, hZt⟩ := hcube
  set law := (Cutoff.cutoffSampleLaw M).toMeasure with hlaw
  -- the two clamped squared witnesses
  set U : Cutoff.CutoffSample d → ℝ := fun omega => 2 * max (Y omega) 0 ^ 2 with hUdef
  set V : Cutoff.CutoffSample d → ℝ := fun omega => 2 * max (Z omega) 0 ^ 2 with hVdef
  have hUm : Measurable U := ((hYm.max measurable_const).pow_const 2).const_mul 2
  have hVm : Measurable V := ((hZm.max measurable_const).pow_const 2).const_mul 2
  have hU0 : ∀ omega, 0 ≤ U omega := fun omega => by positivity
  have hV0 : ∀ omega, 0 ≤ V omega := fun omega => by positivity
  -- squaring: `(2, 1/2) ↦ (1, 1/4)`, amplitudes squared, factor `2` from `(a+b)²`
  have hUt : IsBigOWith law (gammaSigma 1) U (2 * A1 ^ 2) := by
    have hsq : IsBigOWith law (gammaSigma (2 / 2))
        (fun omega => max (Y omega) 0 ^ 2) (A1 ^ 2) :=
      (Provider.Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg hA1.le
        (fun omega => le_max_right _ _)).1 (isBigOWith_max_zero hA1 hYt)
    rw [show (2 : ℝ) / 2 = 1 from by norm_num] at hsq
    exact hsq.const_mul (by norm_num)
  have hVt : IsBigOWith law (gammaSigma (1 / 4)) V (2 * A2 ^ 2) := by
    have hsq : IsBigOWith law (gammaSigma (1 / 2 / 2))
        (fun omega => max (Z omega) 0 ^ 2) (A2 ^ 2) :=
      (Provider.Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg hA2.le
        (fun omega => le_max_right _ _)).1 (isBigOWith_max_zero hA2 hZt)
    rw [show (1 : ℝ) / 2 / 2 = 1 / 4 from by norm_num] at hsq
    exact hsq.const_mul (by norm_num)
  -- the per-cube domination, at every real centre
  have hpt : ∀ (z : Vec d) (omega : Cutoff.CutoffSample d),
      errorAtomSq M n s z omega ≤ U (Cutoff.translateCutoffSample z omega) +
        V (Cutoff.translateCutoffSample z omega) := by
    intro z omega
    set w := Cutoff.translateCutoffSample z omega with hw
    have hE0 : 0 ≤ Support.annularErrorObservable M n s w :=
      Support.annularErrorObservable_nonneg M n s w
    have hle : Support.annularErrorObservable M n s w ≤ max (Y w) 0 + max (Z w) 0 :=
      le_trans (hdom w) (add_le_add (le_max_left _ _) (le_max_left _ _))
    calc errorAtomSq M n s z omega
        = Support.annularErrorObservable M n s w ^ 2 := rfl
      _ ≤ (max (Y w) 0 + max (Z w) 0) ^ 2 := pow_le_pow_left₀ hE0 hle 2
      _ ≤ 2 * max (Y w) 0 ^ 2 + 2 * max (Z w) 0 ^ 2 := sq_add_le_two_mul _ _
  -- the two maxima
  set Umax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax (latticeAnnulusFinset d n j (j - 1))
      (fun v => U (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
    with hUmax
  set Vmax : Cutoff.CutoffSample d → ℝ := fun omega =>
    fmax (latticeAnnulusFinset d n j (j - 1))
      (fun v => V (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega))
    with hVmax
  have hUmaxm : Measurable Umax :=
    measurable_fmax _ fun v =>
      hUm.comp (Cutoff.measurable_translateCutoffSample _)
  have hVmaxm : Measurable Vmax :=
    measurable_fmax _ fun v =>
      hVm.comp (Cutoff.measurable_translateCutoffSample _)
  have hUmaxt : IsBigOWith law (gammaSigma 1) Umax
      (annulusPenalty d 1 (j - n).toNat * (2 * A1 ^ 2)) :=
    isBigOWith_fmax _ (by norm_num) (by positivity)
      (one_le_annulusPenalty d (by norm_num) _)
      (log_card_le_annulusPenalty_rpow_sub_one d (by norm_num) n j (j - 1))
      (fun v _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hUm hUt)
  have hVmaxt : IsBigOWith law (gammaSigma (1 / 4)) Vmax
      (annulusPenalty d (1 / 4) (j - n).toNat * (2 * A2 ^ 2)) :=
    isBigOWith_fmax _ (by norm_num) (by positivity)
      (one_le_annulusPenalty d (by norm_num) _)
      (log_card_le_annulusPenalty_rpow_sub_one d (by norm_num) n j (j - 1))
      (fun v _ => isBigOWith_comp_measurePreserving
        (GoodEvents.measurePreserving_translateCutoffSample M _) hVm hVt)
  have hpen1 : (0 : ℝ) < annulusPenalty d 1 (j - n).toNat * (2 * A1 ^ 2) := by
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1) (j - n).toNat
    have h2 : (0 : ℝ) < 2 * A1 ^ 2 := by positivity
    exact mul_pos (lt_of_lt_of_le zero_lt_one h1) h2
  have hpen2 : (0 : ℝ) < annulusPenalty d (1 / 4) (j - n).toNat * (2 * A2 ^ 2) := by
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1 / 4) (j - n).toNat
    have h2 : (0 : ℝ) < 2 * A2 ^ 2 := by positivity
    exact mul_pos (lt_of_lt_of_le zero_lt_one h1) h2
  refine Provider.Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    (Probability.isAdmissibleTail_gammaSigma (by norm_num))
    hpen1 hpen2 (measurable_errorAnnMax M s j n) hUmaxm hVmaxm
    (Filter.Eventually.of_forall fun omega => ?_) hUmaxt hVmaxt
  exact fmax_le_add_fmax _ _ _ _ fun v _ => hpt _ omega

/-! ## 4. Summability of the weighted penalties -/

/-- The lattice penalty at a reciprocal-integer Orlicz index is a natural power:
at `σ = 1` it is the manuscript's linear `(j−n+1)` and at `σ = 1/4` its fourth
power. -/
theorem annulusPenalty_natPow (d : ℕ) {N : ℕ} (hN : 0 < N) (p : ℕ) :
    annulusPenalty d ((N : ℝ)⁻¹) p = (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ^ N := by
  have hNne : ((N : ℝ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  rw [annulusPenalty, inv_inv]
  exact Real.rpow_natCast _ N

private theorem summable_succ_pow_geometric {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (N : ℕ) : Summable fun i : ℕ => ((i : ℝ) + 1) ^ N * r ^ i := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have hbase := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) N hnorm
  have hshift : Summable fun i : ℕ => (((i + 1 : ℕ) : ℝ)) ^ N * r ^ (i + 1) :=
    hbase.comp_injective (add_left_injective 1)
  refine (hshift.mul_left r⁻¹).congr fun i => ?_
  have hrne : r ≠ 0 := ne_of_gt hr0
  push_cast
  field_simp
  ring

/-- **The weighted lattice penalties of the `𝒢₂` lane are summable**, at every
positive rate and every reciprocal-integer Orlicz index.  This is the input the
countable triangle inequality consumes; the manuscript performs the same estimate
implicitly when it writes the closed forms `s^{-4}` and `s^{-5}`. -/
theorem summable_weightThird_mul_annulusPenalty (d : ℕ) {sprime A : ℝ} {N : ℕ}
    (hsprime : 0 < sprime) (hN : 0 < N) (hA : 0 ≤ A) :
    Summable fun i : ℕ =>
      weightThird sprime (i + 1) * (annulusPenalty d ((N : ℝ)⁻¹) (i + 1) * A) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set r : ℝ := (3 : ℝ) ^ (-sprime) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr, show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith only [hsprime])
  set B : ℝ := (1 + 2 * (d : ℝ) * Real.log 3) ^ N with hB
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hmaj : Summable fun i : ℕ => A * B * r * (((i : ℝ) + 1) ^ N * r ^ i) :=
    (summable_succ_pow_geometric hr0 hr1 N).mul_left (A * B * r)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · have hpen : (0 : ℝ) ≤ annulusPenalty d ((N : ℝ)⁻¹) (i + 1) := by
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      exact le_trans zero_le_one
        (one_le_annulusPenalty d (by positivity) _)
    exact mul_nonneg (weightThird_pos _).le (mul_nonneg hpen hA)
  · -- the penalty base is at most `(1 + 2 d log 3)(i+1)`
    have hbase : 1 + (d : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) * Real.log 3
        ≤ (1 + 2 * (d : ℝ) * Real.log 3) * ((i : ℝ) + 1) := by
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hcast : (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hprod : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 * (i : ℝ) := by positivity
      have hprod2 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 * (i : ℝ) := by positivity
      linarith only [hprod, hprod2, hi]
    have hnn : (0 : ℝ) ≤ 1 + (d : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) * Real.log 3 := by
      positivity
    have hpow : annulusPenalty d ((N : ℝ)⁻¹) (i + 1) ≤ B * (((i : ℝ) + 1) ^ N) := by
      rw [annulusPenalty_natPow d hN, hB, ← mul_pow]
      exact pow_le_pow_left₀ hnn hbase N
    have hwt : weightThird sprime (i + 1) = r * r ^ i := by
      rw [weightThird, hr, pow_succ]
      ring
    have hstep : annulusPenalty d ((N : ℝ)⁻¹) (i + 1) * A ≤ B * ((i : ℝ) + 1) ^ N * A :=
      mul_le_mul_of_nonneg_right hpow hA
    calc weightThird sprime (i + 1) * (annulusPenalty d ((N : ℝ)⁻¹) (i + 1) * A)
        ≤ weightThird sprime (i + 1) * (B * ((i : ℝ) + 1) ^ N * A) :=
          mul_le_mul_of_nonneg_left hstep (weightThird_pos _).le
      _ = A * B * r * (((i : ℝ) + 1) ^ N * r ^ i) := by rw [hwt]; ring

/-! ## 5. Step 2 — the `X_j` Orlicz bound -/

/-- **Step 2, `e.Xj.Orlicz.bound`.**

The atom `X_j` (without the lane prefactor `K₂ε^{−2}`) inherits a two-term
display from Step 1 through the countable generalized triangle inequality,
applied at `σ = 1` and `σ = 1/4` simultaneously.

`hcube` is the per-inner-scale conditional A obligation of Step 1. -/
theorem isTwoTermBigOWith_Xcal (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    {A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hcube : ∀ n : ℤ, n ≤ j - 1 →
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma (1 / 4))
      (fun omega => (XcalE M s j omega).toReal)
      (gammaTriangleConst 1 * ∑' i : ℕ, weightThird ((s : ℝ) / 4) (i + 1) *
        (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)))
      (gammaTriangleConst (1 / 4) * ∑' i : ℕ, weightThird ((s : ℝ) / 4) (i + 1) *
        (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))) := by
  have hs4 : (0 : ℝ) < (s : ℝ) / 4 := by have := s.2; linarith only [this]
  have hpen1pos : ∀ i : ℕ, (0 : ℝ) < annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1) (i + 1)
    exact mul_pos (lt_of_lt_of_le zero_lt_one h1) (by positivity)
  have hpen2pos : ∀ i : ℕ, (0 : ℝ) < annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2) := by
    intro i
    have h1 := one_le_annulusPenalty d (by norm_num : (0 : ℝ) < 1 / 4) (i + 1)
    exact mul_pos (lt_of_lt_of_le zero_lt_one h1) (by positivity)
  have hsum1 : Summable fun i : ℕ =>
      weightThird ((s : ℝ) / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2)) := by
    have h := summable_weightThird_mul_annulusPenalty (d := d) (A := 2 * A1 ^ 2)
      (N := 1) hs4 (by norm_num) (by positivity)
    simpa only [Nat.cast_one, inv_one] using h
  have hsum2 : Summable fun i : ℕ =>
      weightThird ((s : ℝ) / 4) (i + 1) *
        (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)) := by
    have h := summable_weightThird_mul_annulusPenalty (d := d) (A := 2 * A2 ^ 2)
      (N := 4) hs4 (by norm_num) (by positivity)
    have hcast : (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 := by norm_num
    simpa only [hcast] using h
  have hterm : ∀ i : ℕ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 1) (gammaSigma (1 / 4))
        (errorAnnMax M s j (j - 1 - (i : ℤ)))
        (annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2))
        (annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2)) := by
    intro i
    have hidx : (j - (j - 1 - (i : ℤ))).toNat = i + 1 := by omega
    have hbase := isTwoTermBigOWith_errorAnnMax M s j (j - 1 - (i : ℤ))
      (hcube _ (by omega))
    rwa [hidx] at hbase
  have hmain := isTwoTermBigOWith_wsum
    (T := fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
    (c := fun i => weightThird ((s : ℝ) / 4) (i + 1))
    (a1 := fun i => annulusPenalty d 1 (i + 1) * (2 * A1 ^ 2))
    (a2 := fun i => annulusPenalty d (1 / 4) (i + 1) * (2 * A2 ^ 2))
    (by norm_num) (by norm_num)
    (fun i omega => errorAnnMax_nonneg M s j _ omega)
    (fun i => measurable_errorAnnMax M s j _)
    (fun i => weightThird_pos _) hpen1pos hpen2pos hsum1 hsum2 hterm
  have hrw : (fun omega => (XcalE M s j omega).toReal) =
      wsum (fun i => errorAnnMax M s j (j - 1 - (i : ℤ)))
        (fun i => weightThird ((s : ℝ) / 4) (i + 1)) := by
    funext omega
    rw [XcalE_eq_wsumE M s j omega]
    rfl
  rw [hrw]
  exact hmain

end

end Algsuperdiff.Section4.Provider.Proportion
