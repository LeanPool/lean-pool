/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LargeWaves
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShellColumnIndep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.SmallWaves
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroEngine
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.WindowAmplitudes

/-!
# LayerBrackets

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 and Step-3 layer brackets of the kicking lemma

ABK26, §4.2, `l.minimal.scale.sep`, Steps 2 and 3.  Steps 2 and 3 both run on
*layer variables*: the `3^{(2−γ)·}`-weighted volume-normalized shell gauges

```
  Y_l  := 3^{(2−γ)l} ‖∇j_l‖_{W^{1,∞}(□_l)}                            (Step 2)
  G_i^k := 3^{(2−γ)i} max_{z ∈ 3^iℤ^d ∩ □_k} ‖j_i‖_{W^{2,∞}(z+□_i)}    (Step 3)
```

(Step 2's display is ABK26, Step 3's is.)

together with the per-layer `Γ₂` tails `Y_l ≤ 𝒪_{Γ₂}(C)`,
`3^{(2−γ)i}‖j_i‖_{W^{2,∞}(z+□_i)} ≤ 𝒪_{Γ₂}(C)` and the lattice maximum `G_i^k
≤ 𝒪_{Γ₂}(C(k+1−i)^{1/2})` (`e.maxy.bound`).

## The layer variables are the §4.1 atoms, not new objects

The §4.1 proportion lane already renders both brackets at exactly this
repository's carrier, and both per-layer tails are proved there:

* `Proportion.atomG1a M l = 3^{(2−γ)l}‖∇j_l‖_{W^{1,∞}(□_l)}` with
  `Proportion.isBigOWith_atomG1a` at amplitude `1`;
* `Proportion.atomG1b M i z = 3^{(2−γ)i}‖j_i‖_{W^{2,∞}(z+□_i)}` with
  `Proportion.isBigOWith_atomG1b` at the amplitude `atomG1bScale`, *uniformly in
  the base point `z`*;
* `Proportion.scoreG1b M k i = fmax` of `atomG1b M i (3^i v)` over
  `v ∈ latticeCubeFinset d i k`, with `Proportion.isBigOWith_scoreG1b` at the
  machine-computed union-bound penalty `annulusPenalty d 2 (k−i).toNat`.

No layer variable is therefore *defined* here.

## The same tail at every translate, not weakened

`e.maxy.bound` needs one common amplitude at every lattice centre.

## The `ℝ≥0∞` reconciliation

The manuscript's `D₂(k)` and `D₃(k)` are sums over infinitely many layers.  `{n
// n ≤ m}`), which is total; the real-valued reading is `.toReal`, which is `0`
at the divergent samples and hence only strengthens every upper-tail statement.
Two services are needed downstream and proved here:

* `wsum_eq_tsum` — for nonnegative layers the `ℝ≥0∞`-formed weighted series
  `Proportion.wsum` *equals* the real `tsum` at every sample point (both are the
  junk value `0` exactly when the family is not summable).  This is what lets the
  carrier-free window arithmetic of `Algsuperdiff.Probability.WindowRearrange`
  (stated for real `tsum`s) act on the anchor-shaped objects.
* `ae_wsumE_ne_top` — a weighted layer series with summable weighted *first
  moments* is almost surely finite.  This is the honest discharge of the
  convergence side condition that the manuscript never mentions: it is proved
  from the per-layer tails, never assumed.

## References

* ABK26, `l.minimal.scale.sep`, Step 2 and Step 3.
* ABK26, `e.maxy.bound`, `e.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The layer gradient tail -/

/-- This is `Proportion.score_le_wt_mul_atomG1a` at `sprime = 1 − γ`, with the row
weight `wt` unfolded.  It never enlarges the cube: the comparison is between
`□_k` and `□_l` at the *same* centre with both `3^{(2−γ)·}` prefactors
attached, and the printed majorant `3^{(2−γ)(m∧l)}‖∇j_l‖_{W^{1,∞}(□_l)}` is
never formed. -/
theorem gradCross_le (M : ABKModel d) {k l : ℤ} (hkl : k ≤ l)
    (omega : Cutoff.CutoffSample d) :
    Real.rpow 3 ((2 - M.gamma) * (k : ℝ)) * shellW1InfGradNorm k (omega.1 l) ≤
      (3 : ℝ) ^ (-((1 - M.gamma) * ((l - k : ℤ) : ℝ))) *
        (Real.rpow 3 ((2 - M.gamma) * (l : ℝ)) * shellW1InfGradNorm l (omega.1 l)) := by
  have hbase := score_le_wt_mul_atomG1a M (sprime := 1 - M.gamma) le_rfl hkl omega
  have hwt : wt (1 - M.gamma) k l = (3 : ℝ) ^ (-((1 - M.gamma) * ((l - k : ℤ) : ℝ))) := by
    have hkl' : ((k : ℤ) : ℝ) ≤ ((l : ℤ) : ℝ) := by exact_mod_cast hkl
    have hid : idist k l = ((l - k : ℤ) : ℝ) := by
      simp only [idist]
      rw [abs_of_nonpos (by linarith only [hkl'])]
      push_cast
      ring
    rw [wt, hid]
  rw [hwt] at hbase
  exact hbase

/-! ## 2. The layer Hessian tail -/

/-! ## 3. The Step-3 lattice maximum (`e.maxy.bound`) -/

def latticeMaxAmp (d : ℕ) : ℝ := Real.sqrt (1 + (d : ℝ) * Real.log 3) * atomG1bScale

theorem latticeMaxAmp_pos (d : ℕ) : 0 < latticeMaxAmp d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : (0 : ℝ) < 1 + (d : ℝ) * Real.log 3 := by positivity
  exact mul_pos (Real.sqrt_pos.2 hbase) atomG1bScale_pos

/-- The union-bound penalty in the manuscript's `(k+1−i)^{1/2}` shape. -/
private theorem annulusPenalty_two_le (d : ℕ) {i k : ℤ} (hik : i ≤ k) :
    annulusPenalty d 2 (k - i).toNat * atomG1bScale ≤
      latticeMaxAmp d * Real.sqrt (((k + 1 - i : ℤ) : ℝ)) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcast : (((k - i).toNat : ℕ) : ℝ) + 1 = ((k + 1 - i : ℤ) : ℝ) := by
    have hz : (((k - i).toNat : ℕ) : ℤ) = k - i := Int.toNat_of_nonneg (by omega)
    have hz' : ((((k - i).toNat : ℕ) : ℤ) : ℝ) = ((k - i : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hz
    push_cast at hz' ⊢
    linarith only [hz']
  have hone : (1 : ℝ) ≤ ((k + 1 - i : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ k + 1 - i := by omega
    exact_mod_cast this
  have hbase : (0 : ℝ) ≤ 1 + (d : ℝ) * Real.log 3 := by positivity
  have hstep : 1 + (d : ℝ) * ((((k - i).toNat : ℕ) : ℝ) + 1) * Real.log 3 ≤
      (1 + (d : ℝ) * Real.log 3) * ((k + 1 - i : ℤ) : ℝ) := by
    rw [hcast]
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hdl : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := mul_nonneg hd hlog
    have hmul : (d : ℝ) * ((k + 1 - i : ℤ) : ℝ) * Real.log 3
        = (d : ℝ) * Real.log 3 * ((k + 1 - i : ℤ) : ℝ) := by ring
    have hprod : (1 + (d : ℝ) * Real.log 3) * ((k + 1 - i : ℤ) : ℝ)
        = ((k + 1 - i : ℤ) : ℝ) + (d : ℝ) * Real.log 3 * ((k + 1 - i : ℤ) : ℝ) := by
      ring
    rw [hmul, hprod]
    linarith only [hone]
  have hpen : annulusPenalty d 2 (k - i).toNat ≤
      Real.sqrt (1 + (d : ℝ) * Real.log 3) * Real.sqrt (((k + 1 - i : ℤ) : ℝ)) := by
    have hsqrt : annulusPenalty d 2 (k - i).toNat
        = Real.sqrt (1 + (d : ℝ) * ((((k - i).toNat : ℕ) : ℝ) + 1) * Real.log 3) := by
      rw [annulusPenalty, Real.sqrt_eq_rpow]
      norm_num
    rw [hsqrt, ← Real.sqrt_mul hbase]
    exact Real.sqrt_le_sqrt hstep
  rw [latticeMaxAmp]
  have hcomm : Real.sqrt (1 + (d : ℝ) * Real.log 3) * atomG1bScale *
        Real.sqrt (((k + 1 - i : ℤ) : ℝ))
      = Real.sqrt (1 + (d : ℝ) * Real.log 3) * Real.sqrt (((k + 1 - i : ℤ) : ℝ)) *
        atomG1bScale := by ring
  rw [hcomm]
  exact mul_le_mul_of_nonneg_right hpen atomG1bScale_pos.le

/-- **`e.maxy.bound` at the Step-3 lattice cube**:

`max_{z ∈ 3^iℤ^d ∩ □_k} 3^{(2−γ)i}‖j_i‖_{W^{2,∞}(z+□_i)} ≤ 𝒪_{Γ₂}(C(k+1−i)^{1/2})`

at `C = latticeMaxAmp d`, for every `i ≤ k`.  The maximum is
`Proportion.scoreG1b M k i`, the `0`-floored maximum over the explicit lattice
`Finset`; the tail is the proved `Proportion.isBigOWith_scoreG1b` with its
union-bound penalty put into the manuscript's `√`-shape.  The amplitude is
exactly the summand shape consumed by
`Algsuperdiff.Probability.sum_windowAmp_le` and
`Algsuperdiff.Probability.sum_headAmp_le`. -/
theorem isBigOWith_hessLatticeMax (M : ABKModel d) {i k : ℤ} (hik : i ≤ k) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) (scoreG1b M k i)
      (latticeMaxAmp d * Real.sqrt (((k + 1 - i : ℤ) : ℝ))) :=
  (isBigOWith_scoreG1b M k i).mono_scale (annulusPenalty_two_le d hik)

/-! ## 4. Layer independence across shells -/

/-- **The Step-2 layer family is independent** ("by the independence of the
sequence `{j_n}`").  Every layer bracket is a functional of its own shell, and
the single-shell sigma-fields are mutually independent under the cutoff sample
law (`Proportion.iIndep_shellSigma`, the proved form of the frozen
`ShellLawPrefix.independent`). -/
theorem iIndepFun_gradLayer (M : ABKModel d) :
    ProbabilityTheory.iIndepFun
      (fun l : ℤ => fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 ((2 - M.gamma) * (l : ℝ)) * shellW1InfGradNorm l (omega.1 l))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  Algsuperdiff.Section4.Probability.iIndepFun_of_iIndep_sigma (iIndep_shellSigma M)
    fun l => shellLocal_arrayG1a M l l

/-- **The Step-3 in-window layer family is independent.**  A weighted finite sum
of lattice maxima at the *fixed* inner scale `i` over outer cubes `k` is a
functional of the shell `j_i` alone, so the family is independent across `i`.
The weights and the outer window are arbitrary: they enter only deterministically.
-/
theorem iIndepFun_scoreG1b_windowSum (M : ABKModel d) (w : ℤ → ℤ → ℝ) (n m : ℤ) :
    ProbabilityTheory.iIndepFun
      (fun i : ℤ => fun omega : Cutoff.CutoffSample d =>
        ∑ k ∈ Finset.Icc (max n i) m, w i k * scoreG1b M k i omega)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  refine Algsuperdiff.Section4.Probability.iIndepFun_of_iIndep_sigma (iIndep_shellSigma M)
    fun i => ?_
  let : MeasurableSpace (Cutoff.CutoffSample d) := shellSigma d i
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (shellLocal_scoreG1b M k i).const_mul (w i k)

/-! ## 5. First moments from the per-layer tails -/

/-- A nonnegative variable with a `Γ_σ` upper tail has a first moment bounded by
`gammaMomentConst σ` times its scale.  This is `e.moments.OGamma2` in the form
Steps 2 and 3 consume; the two-sided `IsBigO` needed by the moment lemma is the
one-sided tail, because the variable is nonnegative. -/
theorem integral_le_of_isBigOWith_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : Omega → ℝ} {K : ℝ} (hK : 0 < K)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXm : Measurable X)
    (hX : IsBigOWith P (gammaSigma 2) X K) :
    ∫ omega, X omega ∂P ≤ gammaMomentConst 2 * K :=
  Algsuperdiff.Probability.integral_le_of_isBigO_gammaSigma (by norm_num) hK hXm.aemeasurable
    (Algsuperdiff.Probability.isBigO_of_isBigOWith_of_nonneg hX0 hX)

/-- A nonnegative variable with a `Γ_σ` upper tail is integrable. -/
theorem integrable_of_isBigOWith_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : Omega → ℝ} {K : ℝ} (hK : 0 < K)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXm : Measurable X)
    (hX : IsBigOWith P (gammaSigma 2) X K) : Integrable X P :=
  Algsuperdiff.Probability.integrable_of_isBigO_gammaSigma (by norm_num) hK hXm.aemeasurable
    (Algsuperdiff.Probability.isBigO_of_isBigOWith_of_nonneg hX0 hX)

/-! ## 6. The `ℝ≥0∞` / `ℝ` reconciliation of an infinite layer sum -/

section Series

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- **The `ℝ≥0∞`-formed weighted layer series is the real `tsum`.**  For
nonnegative layers and nonnegative weights the two readings agree at *every*
sample point: where the family is summable both are the sum, and where it is not
both are the junk value `0` (`ℝ≥0∞` sum `⊤`, hence `.toReal = 0`).

This is the bridge that lets the carrier-free real window arithmetic of
`Algsuperdiff.Probability.WindowRearrange` act on the anchor-shaped `ℝ≥0∞`
objects. -/
theorem wsum_eq_tsum {T : ℕ → Omega → ℝ} {c : ℕ → ℝ} (hT0 : ∀ j omega, 0 ≤ T j omega)
    (hc : ∀ j, 0 ≤ c j) (omega : Omega) :
    wsum T c omega = ∑' j : ℕ, c j * T j omega := by
  have hterm : ∀ j : ℕ, 0 ≤ c j * T j omega := fun j => mul_nonneg (hc j) (hT0 j omega)
  by_cases hsum : Summable fun j : ℕ => c j * T j omega
  · have h := ENNReal.ofReal_tsum_of_nonneg hterm hsum
    rw [wsum, wsumE, ← h, ENNReal.toReal_ofReal (tsum_nonneg hterm)]
  · have htop : wsumE T c omega = (⊤ : ℝ≥0∞) := by
      by_contra hne
      refine hsum ?_
      have hcoe : ∀ j : ℕ, (((c j * T j omega).toNNReal : ℝ≥0) : ℝ) = c j * T j omega :=
        fun j => Real.coe_toNNReal _ (hterm j)
      have hne' : (∑' j : ℕ, (((c j * T j omega).toNNReal : ℝ≥0) : ℝ≥0∞)) ≠ (⊤ : ℝ≥0∞) := by
        rw [show (fun j : ℕ => (((c j * T j omega).toNNReal : ℝ≥0) : ℝ≥0∞))
            = fun j : ℕ => ENNReal.ofReal (c j * T j omega) from rfl]
        exact hne
      have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.1 hne'
      exact hs.congr hcoe
    rw [wsum, htop, tsum_eq_zero_of_not_summable hsum, ENNReal.toReal_top]

/-- **A weighted layer series with summable weighted first moments is almost
surely finite.**  This is the honest discharge of the convergence side condition
that the manuscript never states: `∫⁻ ∑'_j c_j T_j = ∑'_j c_j ∫ T_j` by Tonelli,
which is finite, so the `ℝ≥0∞` series is finite almost everywhere.  Only the
per-layer first moments enter, and those come from the per-layer `Γ₂` tails. -/
theorem ae_wsumE_ne_top {P : Measure Omega} {T : ℕ → Omega → ℝ} {c a : ℕ → ℝ}
    (hT0 : ∀ j omega, 0 ≤ T j omega) (hTm : ∀ j, Measurable (T j))
    (hTi : ∀ j, Integrable (T j) P) (hc : ∀ j, 0 ≤ c j) (ha : ∀ j, 0 ≤ a j)
    (hmean : ∀ j, ∫ omega, T j omega ∂P ≤ a j)
    (hsum : Summable fun j : ℕ => c j * a j) :
    ∀ᵐ omega ∂P, wsumE T c omega ≠ (⊤ : ℝ≥0∞) := by
  have hmeas : ∀ j : ℕ, Measurable fun omega => ENNReal.ofReal (c j * T j omega) :=
    fun j => ((hTm j).const_mul (c j)).ennreal_ofReal
  have hlint : ∀ j : ℕ, ∫⁻ omega, ENNReal.ofReal (c j * T j omega) ∂P
      ≤ ENNReal.ofReal (c j * a j) := by
    intro j
    have hint : Integrable (fun omega => c j * T j omega) P := (hTi j).const_mul (c j)
    have hnn : 0 ≤ᵐ[P] fun omega => c j * T j omega :=
      Filter.Eventually.of_forall fun omega => mul_nonneg (hc j) (hT0 j omega)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
      MeasureTheory.integral_const_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hmean j) (hc j))
  have hbound : ∫⁻ omega, wsumE T c omega ∂P ≤ ENNReal.ofReal (∑' j : ℕ, c j * a j) := by
    have hswap : ∫⁻ omega, wsumE T c omega ∂P
        = ∑' j : ℕ, ∫⁻ omega, ENNReal.ofReal (c j * T j omega) ∂P := by
      simp only [wsumE]
      exact MeasureTheory.lintegral_tsum fun j => (hmeas j).aemeasurable
    rw [hswap, ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (hc j) (ha j)) hsum]
    exact ENNReal.tsum_le_tsum hlint
  have hne : ∫⁻ omega, wsumE T c omega ∂P ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hae := MeasureTheory.ae_lt_top
    (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun j => hmeas j) hne
  filter_upwards [hae] with omega homega using ne_of_lt homega

end Series

end

end Algsuperdiff.Section4.Provider.MinimalScale
