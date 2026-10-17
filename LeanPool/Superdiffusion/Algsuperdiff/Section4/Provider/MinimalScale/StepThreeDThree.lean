/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepTwoDTwo

/-!
# StepThreeDThree

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 3 of the kicking lemma: the two channels and the `D₃` conclusion

ABK26, §4.2, `l.minimal.scale.sep`, Step 3.  After the rearrangement
(`StepThreeRearrange`) the manuscript's `D₃` sum over the window splits into
two channels, both weighted by the lattice maxima `G_i^k = 3^{(2−γ)i}max_{z ∈
3^iℤ^d ∩ □_k}‖j_i‖_{W^{2,∞}(z+□_i)}`:

```
in-window    (i ∈ [n,m])   :  V_i  = Σ_{k=i}^m 3^{−α(k−i)} G_i^k
below-window (i = n−1−r)   :  H_r  = Σ_{k=n}^m 3^{−α(k−n)} G_{n−1−r}^k
```

(the in-window channel is ABK26, the below-window channel)

with `α = s/4`, and the total is `Σ_{i=n}^m V_i + Σ_{r≥0} 3^{−α(r+1)} H_r`.

This module proves the two `Γ₂` tails and closes the window average.

## The two closures, at the manuscript's own constants

Both channels are `e.Gamma.sigma.triangle` over a finite `k`-range applied to
the lattice maxima, whose amplitudes carry the `e.maxy.bound` penalty
`C(k+1−i)^{1/2}` (`LayerBrackets.isBigOWith_hessLatticeMax`).  The two
deterministic amplitude sums are the proved
`Algsuperdiff.Probability.sum_windowAmp_le` (`Cs^{−3/2}`) and
`Algsuperdiff.Probability.sum_headAmp_le` (per-depth, growing like `√r`), and
the below-window recombination is the proved per-layer geometric closure
`Algsuperdiff.Probability.weightedTsum_isBigOWith_perLayer` at
`Algsuperdiff.Probability.tsum_weight_step3HeadAmp_le`.  The resulting
amplitudes are *byte-identical* to `step3WindowAmp` and `step3TailAmp`: the
sharp Cauchy--Schwarz closure is what makes them `s^{−3/2}` and `s^{−5/2}`
rather than `s^{−2}` and `s^{−3}`.

## The `D₃` bound: the honest `s`-exponent

At `α = s/4` the two channel amplitudes and the depth-swap constant are
(machine-checked in §6 below, `0 < s ≤ 1/2`)

```
K₀ := 3^{α}(1−3^{−α})⁻¹        ≤ 16 s^{−1}
K  := step3WindowAmp C (s/4)   ≤ C' s^{−3/2}
b  := step3TailAmp   C (s/4)   ≤ C'' s^{−5/2}
```

so the window average of the *prefactor-free* `D₃` sum obeys

```
avsum ≤ K₀·C_mom·K  +  𝒪_{Γ₂}( C(K₀K + K₀b)(m−n)^{−1/2} )
      ≤ C s^{−5/2}  +  𝒪_{Γ₂}( C s^{−7/2}(m−n)^{−1/2} ) .
```

Multiplying by the printed prefactor `c⋆^{−1/2}s^{−1}γ^{1/2}` of `D₃` gives the
deterministic level `C c⋆^{−1/2}s^{−7/2}γ^{1/2}` — the printed one — and the
fluctuation scale `C c⋆^{−1/2}s^{−9/2}γ^{1/2}(m−n)^{−1/2}`, which is **one
power of `s` weaker than the printed `s^{−7/2}`** in `e.D3k.kicked`.  The
below-window channel is the culprit: it enters the average with the factor
`(m−n+1)^{−1}` rather than `(m−n+1)^{−1/2}`, and `s^{−9/2}(m−n)^{−1}` is *not*
below `s^{−7/2}(m−n)^{−1/2}` unless `m−n ≥ s^{−2}`, which the lemma does not
assume (it assumes only `n < m`).  A Cesàro reconciliation therefore does not
rescue the printed exponent, and the honest fluctuation exponent is `s^{−9/2}`.

## References

* ABK26, `l.minimal.scale.sep` Step 3; `e.D3k.kicked`; `e.maxy.bound`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Probability
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Step-3 weight and the per-cube amplitude -/

/-- The Step-3 geometric weight `3^{−α p}` at the *real* depth. -/
def stepThreeWeight (alpha : ℝ) (p : ℕ) : ℝ := (3 : ℝ) ^ (-(alpha * (p : ℝ)))

theorem stepThreeWeight_pos (alpha : ℝ) (p : ℕ) : 0 < stepThreeWeight alpha p :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem stepThreeWeight_nonneg (alpha : ℝ) (p : ℕ) : 0 ≤ stepThreeWeight alpha p :=
  (stepThreeWeight_pos alpha p).le

/-- The integer-indexed weight `3^{−α(k−i)}` used inside the channels. -/
def stepThreeWt (alpha : ℝ) (t : ℤ) : ℝ := (3 : ℝ) ^ (-(alpha * ((t : ℤ) : ℝ)))

theorem stepThreeWt_pos (alpha : ℝ) (t : ℤ) : 0 < stepThreeWt alpha t :=
  Real.rpow_pos_of_pos (by norm_num) _

/-! ## 2. The two channels -/

/-- **The in-window channel**: `V_i = Σ_{k=i∨n}^m 3^{−α(k−i)} G_i^k`.  The lower
limit is `n ∨ i` so that the family is defined for every `i ∈ ℤ` — below the
window it is the truncated sum, above the window it is empty, and both cases
obey the same `Γ₂` amplitude. -/
def hessWindow (M : ABKModel d) (alpha : ℝ) (n m i : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ k ∈ Finset.Icc (max n i) m, stepThreeWt alpha (k - i) * scoreG1b M k i omega

/-- **The below-window channel at depth `r`**: `H_r = Σ_{k=n}^m 3^{−α(k−n)}
G_{n−1−r}^k`. -/
def hessHead (M : ABKModel d) (alpha : ℝ) (n m : ℤ) (r : ℕ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑ k ∈ Finset.Icc n m, stepThreeWt alpha (k - n) * scoreG1b M k (n - 1 - (r : ℤ)) omega

theorem hessWindow_nonneg (M : ABKModel d) (alpha : ℝ) (n m i : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ hessWindow M alpha n m i omega :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (stepThreeWt_pos alpha (k - i)).le (scoreG1b_nonneg M k i omega)

theorem hessHead_nonneg (M : ABKModel d) (alpha : ℝ) (n m : ℤ) (r : ℕ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ hessHead M alpha n m r omega :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (stepThreeWt_pos alpha (k - n)).le
      (scoreG1b_nonneg M k (n - 1 - (r : ℤ)) omega)

theorem measurable_hessWindow (M : ABKModel d) (alpha : ℝ) (n m i : ℤ) :
    Measurable (hessWindow M alpha n m i) :=
  Finset.measurable_sum _ fun k _ => (measurable_scoreG1b M k i).const_mul _

theorem measurable_hessHead (M : ABKModel d) (alpha : ℝ) (n m : ℤ) (r : ℕ) :
    Measurable (hessHead M alpha n m r) :=
  Finset.measurable_sum _ fun k _ =>
    (measurable_scoreG1b M k (n - 1 - (r : ℤ))).const_mul _

/-- **The in-window channel family is independent across the inner scale.**  Each
`V_i` is a functional of the shell `j_i` alone. -/
theorem iIndepFun_hessWindow (M : ABKModel d) (alpha : ℝ) (n m : ℤ) :
    ProbabilityTheory.iIndepFun (fun i : ℤ => hessWindow M alpha n m i)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  iIndepFun_scoreG1b_windowSum M (fun i k => stepThreeWt alpha (k - i)) n m

/-! ## 3. The in-window `Γ₂` tail -/

/-- The per-cube amplitude of `e.maxy.bound` at the Step-3 lattice cube. -/
def hessAmp (d : ℕ) : ℝ := latticeMaxAmp d

theorem hessAmp_pos (d : ℕ) : 0 < hessAmp d := latticeMaxAmp_pos d

/-- **The in-window channel has a `Γ₂` tail at the amplitude `step3WindowAmp`**:
`V_i ≤ 𝒪_{Γ₂}(C s^{−3/2})` at `α = s/4`, uniformly in `i` (including below and
above the window).  The route is `e.Gamma.sigma.triangle` over the finite
`k`-range at the `e.maxy.bound` amplitudes, closed by the sharp Cauchy--Schwarz
sum `sum_windowAmp_le`. -/
theorem isBigO_hessWindow (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) {n m : ℤ}
    (hnm : n ≤ m) (i : ℤ) :
    IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (hessWindow M alpha n m i) (step3WindowAmp (hessAmp d) alpha) := by
  have hCv : 0 < hessAmp d := hessAmp_pos d
  rcases le_or_gt i m with him | him
  · -- the honest case: a nonempty `k`-range
    have hne : (Finset.Icc (max n i) m).Nonempty := by
      refine ⟨m, Finset.mem_Icc.mpr ⟨?_, le_rfl⟩⟩
      exact max_le hnm him
    have hsub : Finset.Icc (max n i) m ⊆ Finset.Icc i m := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans (le_max_right n i) hk.1, hk.2⟩
    set a : ℤ → ℝ := fun k =>
      stepThreeWt alpha (k - i) * (hessAmp d * Real.sqrt (((k + 1 - i : ℤ) : ℝ)))
      with hadef
    have hapos : ∀ k ∈ Finset.Icc (max n i) m, 0 < a k := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hik : i ≤ k := le_trans (le_max_right n i) hk.1
      have hsq : (0 : ℝ) < Real.sqrt (((k + 1 - i : ℤ) : ℝ)) := by
        refine Real.sqrt_pos.2 ?_
        have h1 : (0 : ℤ) < k + 1 - i := by omega
        exact_mod_cast h1
      rw [hadef]
      exact mul_pos (stepThreeWt_pos alpha (k - i)) (mul_pos hCv hsq)
    have hX : ∀ k ∈ Finset.Icc (max n i) m,
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
          (fun omega => stepThreeWt alpha (k - i) * scoreG1b M k i omega) (a k) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hik : i ≤ k := le_trans (le_max_right n i) hk.1
      have hbase := (isBigOWith_hessLatticeMax M hik).const_mul
        (c := stepThreeWt alpha (k - i)) (stepThreeWt_pos alpha (k - i)).le
      refine isBigO_of_isBigOWith_of_nonneg (fun omega => ?_) hbase
      exact mul_nonneg (stepThreeWt_pos alpha (k - i)).le (scoreG1b_nonneg M k i omega)
    have htri := isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (Finset.Icc (max n i) m)
      (X := fun k omega => stepThreeWt alpha (k - i) * scoreG1b M k i omega)
      (a := a) (σ := 2) (by norm_num) hne hapos hX
      (fun k _ => (measurable_scoreG1b M k i).const_mul _)
    refine htri.mono_scale ?_
    have hsum : ∑ k ∈ Finset.Icc (max n i) m, a k ≤ hessAmp d * geomSqrtConst alpha := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · intro k _ _
        rw [hadef]
        refine mul_nonneg (stepThreeWt_pos alpha (k - i)).le (mul_nonneg hCv.le ?_)
        exact Real.sqrt_nonneg _
      · exact sum_windowAmp_le halpha hCv.le i m
    have htri0 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    calc gammaTriangleConst 2 * ∑ k ∈ Finset.Icc (max n i) m, a k
        ≤ gammaTriangleConst 2 * (hessAmp d * geomSqrtConst alpha) :=
          mul_le_mul_of_nonneg_left hsum htri0.le
      _ = step3WindowAmp (hessAmp d) alpha := rfl
  · -- above the window the channel is the empty sum
    refine isBigO_gammaSigma_of_eq_zero (step3WindowAmp_pos halpha hCv).le fun omega => ?_
    have hempty : Finset.Icc (max n i) m = (∅ : Finset ℤ) := by
      refine Finset.eq_empty_of_forall_notMem fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have h1 : i ≤ k := le_trans (le_max_right n i) hk.1
      omega
    rw [hessWindow, hempty, Finset.sum_empty]

/-! ## 4. The below-window `Γ₂` tails -/

/-- **The below-window channel at depth `r` has a `Γ₂` tail at the per-depth
amplitude `step3HeadAmp`**.  The amplitude grows like `√r`, which is why the
recombination needs the *per-layer* geometric closure. -/
theorem isBigOWith_hessHead (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) {n m : ℤ}
    (hnm : n ≤ m) (r : ℕ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (hessHead M alpha n m r) (step3HeadAmp (hessAmp d) alpha r) := by
  have hCv : 0 < hessAmp d := hessAmp_pos d
  have hne : (Finset.Icc n m).Nonempty := ⟨m, Finset.mem_Icc.mpr ⟨hnm, le_rfl⟩⟩
  set i : ℤ := n - 1 - (r : ℤ) with hidef
  set a : ℤ → ℝ := fun k =>
    stepThreeWt alpha (k - n) * (hessAmp d * Real.sqrt (((k + 1 - i : ℤ) : ℝ)))
    with hadef
  have hapos : ∀ k ∈ Finset.Icc n m, 0 < a k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hsq : (0 : ℝ) < Real.sqrt (((k + 1 - i : ℤ) : ℝ)) := by
      refine Real.sqrt_pos.2 ?_
      have h1 : (0 : ℤ) < k + 1 - i := by rw [hidef]; omega
      exact_mod_cast h1
    rw [hadef]
    exact mul_pos (stepThreeWt_pos alpha (k - n)) (mul_pos hCv hsq)
  have hX : ∀ k ∈ Finset.Icc n m,
      IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (fun omega => stepThreeWt alpha (k - n) * scoreG1b M k i omega) (a k) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hik : i ≤ k := by rw [hidef]; omega
    have hbase := (isBigOWith_hessLatticeMax M hik).const_mul
      (c := stepThreeWt alpha (k - n)) (stepThreeWt_pos alpha (k - n)).le
    refine isBigO_of_isBigOWith_of_nonneg (fun omega => ?_) hbase
    exact mul_nonneg (stepThreeWt_pos alpha (k - n)).le (scoreG1b_nonneg M k i omega)
  have htri := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (Finset.Icc n m)
    (X := fun k omega => stepThreeWt alpha (k - n) * scoreG1b M k i omega)
    (a := a) (σ := 2) (by norm_num) hne hapos hX
    (fun k _ => (measurable_scoreG1b M k i).const_mul _)
  have hsum := sum_headAmp_le (Cv := hessAmp d) (α := alpha) halpha hCv.le n m r
  have hmono : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (hessHead M alpha n m r) (step3HeadAmp (hessAmp d) alpha r) := by
    refine htri.mono_scale ?_
    have htri0 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    calc gammaTriangleConst 2 * ∑ k ∈ Finset.Icc n m, a k
        ≤ gammaTriangleConst 2 *
            (hessAmp d * (geomSqrtConst alpha + Real.sqrt ((r : ℝ) + 1) * geomTailConst alpha)) :=
          mul_le_mul_of_nonneg_left hsum htri0.le
      _ = step3HeadAmp (hessAmp d) alpha r := rfl
  exact isBigOWith_of_isBigO_of_nonneg (hessHead_nonneg M alpha n m r) hmono

/-- **The below-window channel, recombined**: the weighted series `Σ_{r≥0}
3^{−α(r+1)} H_r`, formed in `ℝ≥0∞` as everywhere else. -/
def hessHeadSeries (M : ABKModel d) (alpha : ℝ) (n m : ℤ) :
    Cutoff.CutoffSample d → ℝ :=
  wsum (fun r => hessHead M alpha n m r) (fun r => stepThreeWeight alpha (r + 1))

theorem hessHeadSeries_nonneg (M : ABKModel d) (alpha : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ hessHeadSeries M alpha n m omega :=
  wsum_nonneg _ _ omega

/-- **The below-window channel closes at `step3TailAmp`** (`𝒪_{Γ₂}(Cs^{−5/2})` at
`α = s/4`). -/
theorem isBigOWith_hessHeadSeries (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha)
    {n m : ℤ} (hnm : n ≤ m) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (hessHeadSeries M alpha n m) (step3TailAmp (hessAmp d) alpha) := by
  have hCv : 0 < hessAmp d := hessAmp_pos d
  -- the plain-weight series, closed by the per-layer geometric closure
  have hbase : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => ∑' r : ℕ,
        (3 : ℝ) ^ (-(alpha * (r : ℝ))) * hessHead M alpha n m r omega)
      (gammaTriangleConst 2 *
        ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r) :=
    weightedTsum_isBigOWith_perLayer (by norm_num)
      (fun r => step3HeadAmp_pos halpha hCv r)
      (summable_weight_step3HeadAmp halpha)
      (fun r omega => hessHead_nonneg M alpha n m r omega)
      (fun r => measurable_hessHead M alpha n m r)
      (fun r => isBigOWith_hessHead M halpha hnm r)
  -- the shifted weight is the plain weight times `3^{−α} ≤ 1`
  have hshift : hessHeadSeries M alpha n m =
      fun omega => (3 : ℝ) ^ (-(alpha * (1 : ℝ))) *
        ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * hessHead M alpha n m r omega := by
    funext omega
    rw [hessHeadSeries, wsum_eq_tsum (fun r w => hessHead_nonneg M alpha n m r w)
      (fun r => stepThreeWeight_nonneg alpha (r + 1)), ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    have hsplit : (3 : ℝ) ^ (-(alpha * ((r + 1 : ℕ) : ℝ)))
        = (3 : ℝ) ^ (-(alpha * (1 : ℝ))) * (3 : ℝ) ^ (-(alpha * (r : ℝ))) := by
      rw [hcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [stepThreeWeight, hsplit, mul_assoc]
  rw [hshift]
  have hone : (3 : ℝ) ^ (-(alpha * (1 : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : 0 < alpha * (1 : ℝ) := by
      rw [mul_one]; exact halpha
    linarith only [this]
  have hmul := hbase.const_mul (c := (3 : ℝ) ^ (-(alpha * (1 : ℝ))))
    (Real.rpow_nonneg (by norm_num) _)
  refine hmul.mono_scale ?_
  have hAmp : 0 ≤ gammaTriangleConst 2 *
      ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r := by
    have h1 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    have h2 : 0 ≤ ∑' r : ℕ,
        (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r :=
      tsum_nonneg fun r =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (step3HeadAmp_nonneg halpha hCv.le r)
    positivity
  calc (3 : ℝ) ^ (-(alpha * (1 : ℝ))) *
        (gammaTriangleConst 2 *
          ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r)
      ≤ 1 * (gammaTriangleConst 2 *
          ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r) :=
        mul_le_mul_of_nonneg_right hone hAmp
    _ = gammaTriangleConst 2 *
          ∑' r : ℕ, (3 : ℝ) ^ (-(alpha * (r : ℝ))) * step3HeadAmp (hessAmp d) alpha r := by
        rw [one_mul]
    _ ≤ step3TailAmp (hessAmp d) alpha := by
        refine mul_le_mul_of_nonneg_left (tsum_weight_step3HeadAmp_le halpha hCv.le)
          gammaTriangleConst_pos.le

/-! ## 5. The `D₃` bound: the window average of the two channels -/

/-- **The Step-3 conclusion at the channel level**.  For a window `n < m` and any
nonnegative depth-swap constant `K₀`, the channel expression produced by the
Step-3 rearrangement splits into a deterministic level and a `Γ₂` fluctuation
of scale `(m−n)^{−1/2}`.

The deterministic level is `K₀·C_mom·step3WindowAmp` and the fluctuation scale is
`cesaroTailEngineConst·(K₀·step3WindowAmp + K₀·step3TailAmp)·(m−n)^{−1/2}`; §6
turns both into explicit powers of `s`. -/
theorem exists_stepThree_channels_kicked (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha)
    {n m : ℤ} (hnm : n < m) {K0 : ℝ} (hK0 : 0 ≤ K0) :
    ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
      (∀ omega,
          K0 * cesaroAvg (fun i => hessWindow M alpha n m i omega) n m
            + (1 / (((m - n + 1 : ℤ) : ℝ))) * (K0 * hessHeadSeries M alpha n m omega)
            ≤ Xdet omega + Xfluc omega) ∧
        (∀ omega, Xdet omega ≤
          K0 * (gammaMomentConst 2 * step3WindowAmp (hessAmp d) alpha)) ∧
        IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
          (cesaroTailEngineConst *
            (K0 * step3WindowAmp (hessAmp d) alpha + K0 * step3TailAmp (hessAmp d) alpha) *
            (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hnm' : n ≤ m := le_of_lt hnm
  have hCv : 0 < hessAmp d := hessAmp_pos d
  have hKpos : 0 < step3WindowAmp (hessAmp d) alpha := step3WindowAmp_pos halpha hCv
  have hbnonneg : 0 ≤ K0 * step3TailAmp (hessAmp d) alpha :=
    mul_nonneg hK0 (step3TailAmp_nonneg halpha hCv.le)
  have hT : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => K0 * hessHeadSeries M alpha n m omega)
      (K0 * step3TailAmp (hessAmp d) alpha) := by
    refine IsBigO.const_mul hK0 ?_
    exact isBigO_of_isBigOWith_of_nonneg (hessHeadSeries_nonneg M alpha n m)
      (isBigOWith_hessHeadSeries M halpha hnm')
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    cesaroAvg_isBigO_of_iIndepFun_with_tail
      (P := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := fun i => hessWindow M alpha n m i)
      (T := fun omega => K0 * hessHeadSeries M alpha n m omega)
      (Dbar := fun omega =>
        K0 * cesaroAvg (fun i => hessWindow M alpha n m i omega) n m
          + (1 / (((m - n + 1 : ℤ) : ℝ))) * (K0 * hessHeadSeries M alpha n m omega))
      (K := step3WindowAmp (hessAmp d) alpha)
      (mu0 := gammaMomentConst 2 * step3WindowAmp (hessAmp d) alpha) (a := K0)
      (b := K0 * step3TailAmp (hessAmp d) alpha)
      hKpos hK0 hbnonneg (iIndepFun_hessWindow M alpha n m)
      (fun i => measurable_hessWindow M alpha n m i)
      (fun i => isBigO_hessWindow M halpha hnm' i)
      (fun i => integral_le_of_isBigOWith_of_nonneg hKpos (hessWindow_nonneg M alpha n m i)
        (measurable_hessWindow M alpha n m i)
        (isBigOWith_of_isBigO_of_nonneg (hessWindow_nonneg M alpha n m i)
          (isBigO_hessWindow M halpha hnm' i)))
      hT n m hnm' (fun _ => le_rfl)
  refine ⟨Xdet, Xfluc, hdom, hdet, ?_⟩
  refine hfluc.mono_scale ?_
  have hpow : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
    have h1 : (0 : ℤ) < m - n := by omega
    exact_mod_cast h1
  have hle : (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) ≤
      (((m - n : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
    refine rpow_neg_half_le_rpow_neg_half hpow ?_
    have h1 : (m - n : ℤ) ≤ m - n + 1 := by omega
    exact_mod_cast h1
  have hA : 0 ≤ cesaroTailEngineConst *
      (K0 * step3WindowAmp (hessAmp d) alpha + K0 * step3TailAmp (hessAmp d) alpha) := by
    have h1 : 0 < cesaroTailEngineConst := cesaroTailEngineConst_pos
    have h2 : 0 ≤ K0 * step3WindowAmp (hessAmp d) alpha := mul_nonneg hK0 hKpos.le
    have h3 : 0 ≤ K0 * step3TailAmp (hessAmp d) alpha := hbnonneg
    positivity
  exact mul_le_mul_of_nonneg_left hle hA

/-! ## 6. The audit: the honest `s`-exponents at `α = s/4` -/

/-- `3^{s/4} ≤ 2` on the Step-3 window `s ≤ 1/2`: the depth-swap constant costs
at most a factor `2`. -/
theorem three_rpow_quarter_le_two {s : ℝ} (hs1 : s ≤ 1 / 2) :
    (3 : ℝ) ^ (s / 4) ≤ 2 := by
  have hstep : (3 : ℝ) ^ (s / 4) ≤ (3 : ℝ) ^ ((1 : ℝ) / 8) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith only [hs1]
  have hbase : (3 : ℝ) ^ ((1 : ℝ) / 8) ≤ (256 : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have h256 : (256 : ℝ) ^ ((1 : ℝ) / 8) = 2 := by
    have h2 : (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) := by norm_num
    rw [h2, ← Real.rpow_natCast (2 : ℝ) 8, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← h256]
  exact le_trans hstep hbase

/-- **The depth-swap constant in closed form**: `3^{s/4}(1−3^{−s/4})⁻¹ ≤ 16 s^{−1}`
on `0 < s ≤ 1/2`. -/
theorem swapConst_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) ≤ 16 * s⁻¹ := by
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have halpha1 : s / 4 ≤ 1 / 2 := by linarith only [hs1]
  have hg : geomTailConst (s / 4) ≤ 8 * s⁻¹ := by
    refine (geomTailConst_le halpha0 halpha1).trans (le_of_eq ?_)
    field_simp
    norm_num
  have hgpos : 0 < geomTailConst (s / 4) := geomTailConst_pos halpha0
  have h3 : (3 : ℝ) ^ (s / 4) ≤ 2 := three_rpow_quarter_le_two hs1
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (s / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs0
  calc (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) ≤ 2 * (8 * s⁻¹) := by
        exact mul_le_mul h3 hg hgpos.le (by norm_num)
    _ = 16 * s⁻¹ := by ring

/-- `geomTailConst (s/4)³ ≤ 512 s^{−3}` — the cube of the closure constant at the
Step-3 rate. -/
theorem geomTailConst_quarter_cube_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    geomTailConst (s / 4) ^ 3 ≤ 512 * s⁻¹ ^ 3 := by
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have halpha1 : s / 4 ≤ 1 / 2 := by linarith only [hs1]
  have hgpos : 0 < geomTailConst (s / 4) := geomTailConst_pos halpha0
  have hg8 : geomTailConst (s / 4) ≤ 8 * s⁻¹ := by
    refine (geomTailConst_le halpha0 halpha1).trans (le_of_eq ?_)
    field_simp
    norm_num
  refine (pow_le_pow_left₀ hgpos.le hg8 3).trans (le_of_eq ?_)
  rw [mul_pow]
  norm_num

/-- **`geomSqrtConst (s/4) ≤ 23 (√s)^{−3}`**, the sharp `Γ₂` closed form at the
Step-3 rate (: the Cauchy--Schwarz closure is what makes the exponent `3/2` and
not `2`). -/
theorem geomSqrtConst_quarter_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    geomSqrtConst (s / 4) ≤ 23 * ((Real.sqrt s) ^ 3)⁻¹ := by
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have hgpos : 0 < geomTailConst (s / 4) := geomTailConst_pos halpha0
  have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hL0 : (0 : ℝ) ≤ geomSqrtConst (s / 4) := (geomSqrtConst_pos halpha0).le
  have hR0 : (0 : ℝ) ≤ 23 * ((Real.sqrt s) ^ 3)⁻¹ := by
    have h1 : (0 : ℝ) < ((Real.sqrt s) ^ 3)⁻¹ := inv_pos.2 (pow_pos hsq0 3)
    linarith only [h1]
  refine le_of_sq_le_sq' hL0 hR0 ?_
  have hLsq : geomSqrtConst (s / 4) ^ 2 = geomTailConst (s / 4) ^ 3 := by
    rw [geomSqrtConst]
    exact Real.sq_sqrt (pow_nonneg hgpos.le 3)
  have hx : ((Real.sqrt s) ^ 3) ^ 2 = s ^ 3 := by
    rw [← pow_mul, show (3 : ℕ) * 2 = 2 * 3 from by norm_num, pow_mul,
      Real.sq_sqrt hs0.le]
  have hRsq : (23 * ((Real.sqrt s) ^ 3)⁻¹) ^ 2 = 529 * s⁻¹ ^ 3 := by
    rw [mul_pow, inv_pow, hx, ← inv_pow]
    norm_num
  rw [hLsq, hRsq]
  have h512 := geomTailConst_quarter_cube_le hs0 hs1
  have hpos : (0 : ℝ) ≤ s⁻¹ ^ 3 := by positivity
  linarith only [h512, hpos]

/-- **The in-window amplitude in closed form** (the printed `Cs^{−3/2}`): `step3WindowAmp C
(s/4) ≤ 23·gammaTriangleConst 2·C·(√s)^{−3}` on `0 < s ≤ 1/2`.  The `(√s)^{−3}`
spelling keeps every numeric tactic away from `rpow`. -/
theorem step3WindowAmp_closed {s Cv : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2)
    (hCv : 0 ≤ Cv) :
    step3WindowAmp Cv (s / 4) ≤
      gammaTriangleConst 2 * (Cv * (23 * ((Real.sqrt s) ^ 3)⁻¹)) := by
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have hgs := geomSqrtConst_quarter_le hs0 hs1
  have hstep : Cv * geomSqrtConst (s / 4) ≤ Cv * (23 * ((Real.sqrt s) ^ 3)⁻¹) :=
    mul_le_mul_of_nonneg_left hgs hCv
  simp only [step3WindowAmp]
  exact mul_le_mul_of_nonneg_left hstep gammaTriangleConst_pos.le

/-- **The below-window amplitude in closed form** (the printed `Cs^{−5/2}`): `step3TailAmp C
(s/4) ≤ gammaTriangleConst 2² · 2C · 8·23 · s^{−1}(√s)^{−3}`. -/
theorem step3TailAmp_closed {s Cv : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (hCv : 0 ≤ Cv) :
    step3TailAmp Cv (s / 4) ≤
      gammaTriangleConst 2 *
        (gammaTriangleConst 2 * (2 * Cv * ((8 * s⁻¹) * (23 * ((Real.sqrt s) ^ 3)⁻¹)))) := by
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have halpha1 : s / 4 ≤ 1 / 2 := by linarith only [hs1]
  have hgt : geomTailConst (s / 4) ≤ 8 * s⁻¹ := by
    refine (geomTailConst_le halpha0 halpha1).trans (le_of_eq ?_)
    field_simp
    norm_num
  have hgs := geomSqrtConst_quarter_le hs0 hs1
  have hgtpos : 0 < geomTailConst (s / 4) := geomTailConst_pos halpha0
  have hgspos : 0 < geomSqrtConst (s / 4) := geomSqrtConst_pos halpha0
  have hprod : geomTailConst (s / 4) * geomSqrtConst (s / 4)
      ≤ (8 * s⁻¹) * (23 * ((Real.sqrt s) ^ 3)⁻¹) :=
    mul_le_mul hgt hgs hgspos.le (by positivity)
  have h2Cv : 0 ≤ 2 * Cv := by linarith only [hCv]
  simp only [step3TailAmp]
  refine mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le
  refine mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le
  exact mul_le_mul_of_nonneg_left hprod h2Cv

/-! ## 7. The two envelopes as explicit powers of `s` -/

/-- The deterministic constant of Step 3, dimension only. -/
def stepThreeDetConst (d : ℕ) : ℝ :=
  368 * gammaTriangleConst 2 * hessAmp d * gammaMomentConst 2

/-- The fluctuation constant of Step 3, dimension only. -/
def stepThreeFlucConst (d : ℕ) : ℝ :=
  cesaroTailEngineConst *
    (368 * gammaTriangleConst 2 * hessAmp d + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d)

/-- The `√`-reciprocal bookkeeping used by the two closed forms. -/
private theorem sqrt_inv_facts {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    0 < (Real.sqrt s)⁻¹ ∧ s⁻¹ = ((Real.sqrt s)⁻¹) ^ 2 ∧
      ((Real.sqrt s) ^ 3)⁻¹ = ((Real.sqrt s)⁻¹) ^ 3 ∧
      ((Real.sqrt s)⁻¹) ^ 5 ≤ ((Real.sqrt s)⁻¹) ^ 7 := by
  have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hupos : (0 : ℝ) < (Real.sqrt s)⁻¹ := inv_pos.2 hsq0
  have hsu : s⁻¹ = ((Real.sqrt s)⁻¹) ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hs0.le]
  have hu3 : ((Real.sqrt s) ^ 3)⁻¹ = ((Real.sqrt s)⁻¹) ^ 3 := by
    rw [inv_pow]
  have hsle : Real.sqrt s ≤ 1 := by
    have h1 : Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith only [hs1])
    rwa [Real.sqrt_one] at h1
  have hu1 : (1 : ℝ) ≤ (Real.sqrt s)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsq0, inv_one]
    exact hsle
  have hmono : ((Real.sqrt s)⁻¹) ^ 5 ≤ ((Real.sqrt s)⁻¹) ^ 7 :=
    pow_le_pow_right₀ hu1 (by norm_num)
  exact ⟨hupos, hsu, hu3, hmono⟩

/-- **The Step-3 deterministic level, closed** (the printed exponent).  At
`α = s/4` the deterministic level of `exists_stepThree_channels_kicked` is at most
`C(d)·s^{−5/2}`; multiplied by the `D₃` prefactor `c⋆^{−1/2}s^{−1}γ^{1/2}` this is
the printed `C c⋆^{−1/2}s^{−7/2}γ^{1/2}` of `e.D3k.kicked`. -/
theorem stepThree_det_closed (d : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) *
        (gammaMomentConst 2 * step3WindowAmp (hessAmp d) (s / 4)) ≤
      stepThreeDetConst d * ((Real.sqrt s) ^ 5)⁻¹ := by
  obtain ⟨hupos, hsu, hu3, _⟩ := sqrt_inv_facts hs0 hs1
  have hT : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hCv : 0 < hessAmp d := hessAmp_pos d
  have hmom : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hK0 : (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) ≤ 16 * ((Real.sqrt s)⁻¹) ^ 2 := by
    have h := swapConst_le hs0 hs1
    rwa [hsu] at h
  have hK0pos : 0 < (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (s / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 < geomTailConst (s / 4) := geomTailConst_pos (by linarith only [hs0])
    positivity
  have hK : step3WindowAmp (hessAmp d) (s / 4) ≤
      gammaTriangleConst 2 * (hessAmp d * (23 * ((Real.sqrt s)⁻¹) ^ 3)) := by
    have h := step3WindowAmp_closed hs0 hs1 hCv.le
    rwa [hu3] at h
  have hu5 : ((Real.sqrt s) ^ 5)⁻¹ = ((Real.sqrt s)⁻¹) ^ 5 := by rw [inv_pow]
  have hstep : gammaMomentConst 2 * step3WindowAmp (hessAmp d) (s / 4) ≤
      gammaMomentConst 2 * (gammaTriangleConst 2 * (hessAmp d * (23 * ((Real.sqrt s)⁻¹) ^ 3))) :=
    mul_le_mul_of_nonneg_left hK hmom.le
  have hprod := mul_le_mul hK0 hstep
    (mul_nonneg hmom.le (step3WindowAmp_pos (by linarith only [hs0]) hCv).le)
    (by positivity)
  rw [hu5, stepThreeDetConst]
  calc ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) *
        (gammaMomentConst 2 * step3WindowAmp (hessAmp d) (s / 4))
      ≤ (16 * ((Real.sqrt s)⁻¹) ^ 2) *
          (gammaMomentConst 2 *
            (gammaTriangleConst 2 * (hessAmp d * (23 * ((Real.sqrt s)⁻¹) ^ 3)))) := hprod
    _ = 368 * gammaTriangleConst 2 * hessAmp d * gammaMomentConst 2 *
          ((Real.sqrt s)⁻¹) ^ 5 := by ring

/-- Multiplied by the `D₃` prefactor `c⋆^{−1/2}s^{−1}γ^{1/2}` this is
`C c⋆^{−1/2}s^{−9/2}γ^{1/2}(m−n)^{−1/2}`, one power of `s` weaker than the printed
`s^{−7/2}` of `e.D3k.kicked`. -/
theorem stepThree_fluc_closed (d : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    cesaroTailEngineConst *
        (((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3WindowAmp (hessAmp d) (s / 4) +
          ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3TailAmp (hessAmp d) (s / 4)) ≤
      stepThreeFlucConst d * ((Real.sqrt s) ^ 7)⁻¹ := by
  obtain ⟨hupos, hsu, hu3, hu57⟩ := sqrt_inv_facts hs0 hs1
  have hT : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hCv : 0 < hessAmp d := hessAmp_pos d
  have halpha0 : (0 : ℝ) < s / 4 := by linarith only [hs0]
  have hK0 : (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) ≤ 16 * ((Real.sqrt s)⁻¹) ^ 2 := by
    have h := swapConst_le hs0 hs1
    rwa [hsu] at h
  have hK0pos : 0 < (3 : ℝ) ^ (s / 4) * geomTailConst (s / 4) := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (s / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 < geomTailConst (s / 4) := geomTailConst_pos halpha0
    positivity
  have hK : step3WindowAmp (hessAmp d) (s / 4) ≤
      gammaTriangleConst 2 * (hessAmp d * (23 * ((Real.sqrt s)⁻¹) ^ 3)) := by
    have h := step3WindowAmp_closed hs0 hs1 hCv.le
    rwa [hu3] at h
  have hb : step3TailAmp (hessAmp d) (s / 4) ≤
      gammaTriangleConst 2 *
        (gammaTriangleConst 2 *
          (2 * hessAmp d *
            ((8 * ((Real.sqrt s)⁻¹) ^ 2) * (23 * ((Real.sqrt s)⁻¹) ^ 3)))) := by
    have h := step3TailAmp_closed hs0 hs1 hCv.le
    rwa [hu3, hsu] at h
  have hwin := mul_le_mul hK0 hK (step3WindowAmp_pos halpha0 hCv).le (by positivity)
  have htail := mul_le_mul hK0 hb (step3TailAmp_nonneg halpha0 hCv.le) (by positivity)
  have hu7 : ((Real.sqrt s) ^ 7)⁻¹ = ((Real.sqrt s)⁻¹) ^ 7 := by rw [inv_pow]
  have hmid : ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3WindowAmp (hessAmp d) (s / 4) +
        ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3TailAmp (hessAmp d) (s / 4)
      ≤ 368 * gammaTriangleConst 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 5
        + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 7 := by
    have he1 : (16 * ((Real.sqrt s)⁻¹) ^ 2) *
          (gammaTriangleConst 2 * (hessAmp d * (23 * ((Real.sqrt s)⁻¹) ^ 3)))
        = 368 * gammaTriangleConst 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 5 := by ring
    have he2 : (16 * ((Real.sqrt s)⁻¹) ^ 2) *
          (gammaTriangleConst 2 *
            (gammaTriangleConst 2 *
              (2 * hessAmp d *
                ((8 * ((Real.sqrt s)⁻¹) ^ 2) * (23 * ((Real.sqrt s)⁻¹) ^ 3)))))
        = 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 7 := by ring
    rw [← he1, ← he2]
    linarith only [hwin, htail]
  have habs : 368 * gammaTriangleConst 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 5
      ≤ 368 * gammaTriangleConst 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 7 := by
    refine mul_le_mul_of_nonneg_left hu57 ?_
    positivity
  rw [hu7, stepThreeFlucConst]
  have hfinal : ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3WindowAmp (hessAmp d) (s / 4) +
        ((3 : ℝ) ^ (s / 4) * geomTailConst (s / 4)) * step3TailAmp (hessAmp d) (s / 4)
      ≤ (368 * gammaTriangleConst 2 * hessAmp d + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d)
          * ((Real.sqrt s)⁻¹) ^ 7 := by
    have hring : (368 * gammaTriangleConst 2 * hessAmp d
          + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d) * ((Real.sqrt s)⁻¹) ^ 7
        = 368 * gammaTriangleConst 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 7
          + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d * ((Real.sqrt s)⁻¹) ^ 7 := by ring
    rw [hring]
    linarith only [hmid, habs]
  have hassoc : cesaroTailEngineConst *
        ((368 * gammaTriangleConst 2 * hessAmp d
            + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d) * ((Real.sqrt s)⁻¹) ^ 7)
      = cesaroTailEngineConst *
          (368 * gammaTriangleConst 2 * hessAmp d
            + 5888 * gammaTriangleConst 2 ^ 2 * hessAmp d) * ((Real.sqrt s)⁻¹) ^ 7 := by
    ring
  rw [← hassoc]
  exact mul_le_mul_of_nonneg_left hfinal cesaroTailEngineConst_pos.le

end

end Algsuperdiff.Section4.Provider.MinimalScale
