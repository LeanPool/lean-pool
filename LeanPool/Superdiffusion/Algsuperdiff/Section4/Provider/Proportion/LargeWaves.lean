/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1AtomTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G1Engine
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.GaugeBridge

/-!
# LargeWaves

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 1 of `l.ratio.of.good.scales.for.k`: the large-waves lane

This module realizes the `𝒢₁a` half of `l.ratio.of.good.scales.for.k`: the
scale-counting variable `X_k` and its cube-comparison link to the first
condition of `𝒢₁`.

## The link `e.counting.scales.G1.Xk.link`

The manuscript's `‖·‖_{W^{1,∞}(□_m)} ≤^{k-m}‖·‖_{W^{1,∞}(□_k)}` for `m ≤ k`
is the proved `GaugeBridge.shellW1InfGradNorm_le_zpow_mul_of_le`, *with
constant `1`* at the exact `p = ∞` gauge.  Combined with the exponent identity
`3^{(2-γ)m} 3^{k-m} = 3^{-(1-γ)(k-m)} 3^{(2-γ)k}` this gives, for `m ≤ k`,

```
3^{(2-γ)m} ‖∇j_k‖_{W^{1,∞}(□_m)} ≤ 3^{-(1-γ)(k-m)} X_k ,
```

which is the manuscript's display with `C = 1`.  The Appendix-D weight rate
`s'` is taken anywhere in `(0, 1-γ]`; the standing assumption `γ ≤ 1/4` of
`ShellLawPrefix` makes `s' = 1/2` always admissible, and `2s' ≤ 1` is what the
row-summability of the engine needs.

## The concentration application (`e.counting.scales.G1.step1.pre`)

The graph's correction records that the application is at level `θ/2` and that
the printed rate denominator `32` over-claims by a bounded factor.  Here
nothing is rounded: the lane is run at the honest rate produced by the proved
`p.concentration.for.scales`, and the `θ/2` level is supplied by the caller.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 1.
* ABK26, `d.good.event.for.lambda`, (the first `𝒢₁` condition).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The first condition of `𝒢₁`, as a named event -/

/-- **The first condition of `𝒢₁(m; s, T)`**: `Σ_{k ≥ m}
3^{(2-γ)m}‖∇j_k‖_{W^{1,∞}(□_m)} ≤ T`, the `ℝ≥0∞` sum of the frozen definition. -/
def eventG1a (M : ABKModel d) (m : ℤ) (T : ℝ) : Set (Cutoff.CutoffSample d) :=
  {omega |
    (∑' k : {k : ℤ // m ≤ k},
      ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
        shellW1InfGradNorm m (omega.1 k.1))) ≤ ENNReal.ofReal T}

/-- **The second condition of `𝒢₁(m; s, T)`**, named for the `½θ` split; it is the
lane of `SmallWaves`. -/
def eventG1b (M : ABKModel d) (m : ℤ) (s T : ℝ) : Set (Cutoff.CutoffSample d) :=
  {omega |
    (∑' n : {n : ℤ // n ≤ m},
      ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
        ∑ k ∈ Finset.Icc (n.1 - 1) m,
          (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
              ⨆ v : ↥(latticeCubeSet d k m),
                ENNReal.ofReal
                  (shellW2InfNormAt (triadicLatticePoint k v.1) k (omega.1 k))) ^ 2) ≤
      ENNReal.ofReal (T ^ 2)}

/-- The frozen `𝒢₁` is the intersection of the two named conditions. -/
theorem eventG1_eq_inter (M : ABKModel d) (m : ℤ) (s T : ℝ) :
    Support.eventG1 M m s T = eventG1a M m T ∩ eventG1b M m s T :=
  rfl

/-! ## 2. The cube-comparison link `e.counting.scales.G1.Xk.link` -/

private theorem rpow_link (gamma : ℝ) (m k : ℤ) :
    Real.rpow 3 ((2 - gamma) * (m : ℝ)) * (3 : ℝ) ^ (k - m) =
      Real.rpow 3 (-((1 - gamma) * ((k : ℝ) - (m : ℝ)))) *
        Real.rpow 3 ((2 - gamma) * (k : ℝ)) := by
  rw [← rpow_intCast_three (k - m), ← rpow_add_three, ← rpow_add_three]
  congr 1
  push_cast
  ring

private theorem idist_of_le {m k : ℤ} (hmk : m ≤ k) :
    idist m k = (k : ℝ) - (m : ℝ) := by
  have hmk' : ((m : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hmk
  simp only [idist]
  rw [abs_of_nonpos (by linarith only [hmk'])]
  ring

/-- **`e.counting.scales.G1.Xk.link`, at constant `1`.**  For `m ≤ k` the `m`-cube
term of `𝒢₁`'s first condition is below the Appendix-D weighted atom, at any
weight rate `s' ≤ 1 - γ`. -/
theorem score_le_wt_mul_atomG1a (M : ABKModel d) {sprime : ℝ}
    (hsle : sprime ≤ 1 - M.gamma) {m k : ℤ} (hmk : m ≤ k)
    (omega : Cutoff.CutoffSample d) :
    Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) * shellW1InfGradNorm m (omega.1 k) ≤
      wt sprime m k * atomG1a M k omega := by
  have hmk' : ((m : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hmk
  have hA : (0 : ℝ) ≤ Real.rpow 3 ((2 - M.gamma) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_left
    (shellW1InfGradNorm_le_zpow_mul_of_le hmk (omega.1 k)) hA
  have hexp : Real.rpow 3 (-((1 - M.gamma) * ((k : ℝ) - (m : ℝ)))) ≤
      Real.rpow 3 (-(sprime * ((k : ℝ) - (m : ℝ)))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hd : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ) := by linarith only [hmk']
    nlinarith only [hsle, hd]
  have hwt : wt sprime m k = Real.rpow 3 (-(sprime * ((k : ℝ) - (m : ℝ)))) := by
    rw [wt, idist_of_le hmk]
    rfl
  calc Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) * shellW1InfGradNorm m (omega.1 k)
      ≤ Real.rpow 3 ((2 - M.gamma) * (m : ℝ)) *
          ((3 : ℝ) ^ (k - m) * shellW1InfGradNorm k (omega.1 k)) := hstep
    _ = (Real.rpow 3 ((2 - M.gamma) * (m : ℝ)) * (3 : ℝ) ^ (k - m)) *
          shellW1InfGradNorm k (omega.1 k) := by ring
    _ = Real.rpow 3 (-((1 - M.gamma) * ((k : ℝ) - (m : ℝ)))) * atomG1a M k omega := by
        rw [rpow_link M.gamma m k, atomG1a]
        ring
    _ ≤ wt sprime m k * atomG1a M k omega := by
        rw [hwt]
        exact mul_le_mul_of_nonneg_right hexp (atomG1a_nonneg M k omega)

/-! ## 3. The Appendix-D array of the large-waves lane -/

/-- **The large-waves Appendix-D array**: the two-index array whose every row is
the atom family `X_k`. -/
def arrayG1a (M : ABKModel d) : ℤ → ℤ → Cutoff.CutoffSample d → ℝ :=
  fun _m k omega => atomG1a M k omega

theorem arrayG1a_nonneg (M : ABKModel d) (m k : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ arrayG1a M m k omega :=
  atomG1a_nonneg M k omega

theorem measurable_arrayG1a (M : ABKModel d) (m k : ℤ) :
    Measurable (arrayG1a M m k) :=
  measurable_atomG1a M k

/-- Each column of the array reads exactly one shell — the (J1) input of the
independence hypothesis. -/
theorem shellLocal_arrayG1a (M : ABKModel d) (m k : ℤ) :
    Measurable[shellSigma d k] (arrayG1a M m k) :=
  measurable_shellSigma_comp k
    ((measurable_shellW1InfGradNorm k).const_mul
      (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))))

theorem isBigOWith_arrayG1a (M : ABKModel d) (m k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (arrayG1a M m k) 1 :=
  isBigOWith_atomG1a M k

/-! ## 4. The deterministic reduction of the lane's bad event -/

/-- **The first `𝒢₁` condition is dominated by the Appendix-D row.**  Pointwise
in `ω`, unconditional, in `ℝ≥0∞`: the one-sided sum of the frozen definition is
below the two-sided Appendix-D row of the array. -/
theorem eventG1a_lhs_le_rowGE (M : ABKModel d) {sprime : ℝ}
    (hsle : sprime ≤ 1 - M.gamma) (m : ℤ) (omega : Cutoff.CutoffSample d) :
    (∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          shellW1InfGradNorm m (omega.1 k.1))) ≤
      rowGE (arrayG1a M) sprime m omega := by
  calc (∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          shellW1InfGradNorm m (omega.1 k.1)))
      ≤ ∑' k : {k : ℤ // m ≤ k},
          ENNReal.ofReal (wt sprime m k.1 * atomG1a M k.1 omega) :=
        ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal
          (score_le_wt_mul_atomG1a M hsle k.2 omega)
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (wt sprime m k * atomG1a M k omega) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun k : ℤ => ENNReal.ofReal (wt sprime m k * atomG1a M k omega))
    _ = rowGE (arrayG1a M) sprime m omega := rfl

/-- Off the lane's good event the `ℝ≥0∞` row exceeds the threshold. -/
theorem lt_rowGE_of_notMem_eventG1a (M : ABKModel d) {sprime T : ℝ}
    (hsle : sprime ≤ 1 - M.gamma) (m : ℤ) {omega : Cutoff.CutoffSample d}
    (hnot : omega ∉ eventG1a M m T) :
    ENNReal.ofReal T < rowGE (arrayG1a M) sprime m omega := by
  rw [eventG1a, Set.mem_ofPred_eq, not_le] at hnot
  exact hnot.trans_le (eventG1a_lhs_le_rowGE M hsle m omega)

end

end Algsuperdiff.Section4.Provider.Proportion
