/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedLargeCubeW1Inf
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.GradSlotMoment

/-!
# GradBottomLayer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# B6, first half completed: the bottom layer of the `L`-free gradient slot

## What this module does

`GradSlotMoment.lean` resolved the `L`-free gradient slot into a deep block
(every shell index at least the cube scale, carrying the `𝒪_{Γ₂}(^{γj})`
display) plus ONE bottom layer `i = j − 1`, read on a cube strictly larger than
its own shell scale.  It is settled here.

The route is the proved covering-plus-maximum machinery of
`Stream/LargeCubeW1Inf.lean` and its translated companion
`Stream/TranslatedLargeCubeW1Inf.lean`: their `largeCubeDerivGauge l k j = 3^k
‖∇j‖_{L^∞(□_l)} + 3^{2k} ‖∇²j‖_{L^∞(□_l)}` is exactly the manuscript's
`e.W1inf.jL.bound.smaller` summand, and
`isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate` prices it, for `k < l`
real base point, at `C(d) (l − k)^{1/2} 3^{γk}`.  Taking the cube scale `l = j`
and the shell scale `k = j − 1` gives `l − k = 1`, so the maximum lemma's `(log
N)^{1/2}` factor is a pure `d`-constant here.

The deterministic bridge is the exact weight arithmetic

```
3^{2j} ‖∇ j_{j−1}‖_{W^{1,∞}(z+□_j)}
    ≤ 3^{2j} ‖∇² j_{j−1}‖_{L^∞(z+□_j)} + 3^{j} ‖∇ j_{j−1}‖_{L^∞(z+□_j)}
    ≤ 9 · largeCubeDerivGauge j (j−1) (translate z j_{j−1}) ,
```

since `9 · 3^{j−1} = 3^{j+1} ≥ 3^{j}` and `9 · 3^{2(j−1)} = 3^{2j}`.  Only
constants move; the amplitude `3^{γ(j−1)} ≤ 3^{γj}` keeps the exponent.

## The assembled slot

Section 3 below glues the bottom layer to `GradSlotMoment`'s deep block through
the single `ℕ`-indexed series

```
fullGradSeries j v ω = Σ_{n ≥ 0} ‖∇ j_{j−1+n}‖_{W^{1,∞}(3^j v + □_j)} ,
```

whose weighted form carries one `𝒪_{Γ₂}(^{γj})` display for the WHOLE `L`-free
gradient slot (`isBigOWith_gammaSigma_weightedFullGradSeries`); the
identification with the slot itself is almost sure, exactly as in
`GradSlotMoment.ae_lFreeGradSlot_eq_bottomLayer_add_deep`.

## References

* ABK26, (`e.nabla.jk.O`), (`e.W.1.inf.bound`), (`e.W1inf.jL.bound.smaller`),
  (bullet (B6), first half).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## 1. The deterministic bridge to the proved large-cube derivative gauge -/

/-- The cube weight of the gradient slot, as an integer power. -/
private theorem rpow_two_mul_eq_zpow (k : ℤ) :
    Real.rpow 3 (2 * (k : ℝ)) = (3 : ℝ) ^ (2 * k) := by
  rw [← Real.rpow_intCast 3 (2 * k)]
  congr 1
  push_cast
  ring

/-- **The bottom-layer weight arithmetic.**  The cube-weighted `W^{1,∞}` gradient
gauge at cube scale `k` is dominated by `9` times the proved large-cube
derivative gauge at cube scale `k` and shell scale `k − 1`. -/
theorem rpow_weighted_shellW1InfGradNorm_le_largeCubeDerivGauge (k : ℤ)
    (f : ShellField d) :
    Real.rpow 3 (2 * (k : ℝ)) * Support.shellW1InfGradNorm k f ≤
      9 * largeCubeDerivGauge k (k - 1) f := by
  have hS : (0 : ℝ) ≤ localCubeSecondDerivNorm k f := localCubeSecondDerivNorm_nonneg k f
  have hD : (0 : ℝ) ≤ localCubeDerivNorm k f := localCubeDerivNorm_nonneg k f
  have hApos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h2k : (0 : ℝ) < (3 : ℝ) ^ (2 * k) := zpow_pos (by norm_num) _
  have hnegpos : (0 : ℝ) < (3 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (2 * k) = (3 : ℝ) ^ k * (3 : ℝ) ^ k := by
    rw [two_mul]
    exact zpow_add₀ (by norm_num) k k
  have hinv : (3 : ℝ) ^ k * (3 : ℝ) ^ (-k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  have h2 : (3 : ℝ) ^ (k - 1) * 3 = (3 : ℝ) ^ k := by
    have hz : (3 : ℝ) ^ (k - 1 + 1) = (3 : ℝ) ^ (k - 1) * (3 : ℝ) ^ (1 : ℤ) :=
      zpow_add₀ (by norm_num) (k - 1) 1
    rw [zpow_one, show k - 1 + 1 = k by ring] at hz
    exact hz.symm
  have h3 : (3 : ℝ) ^ (2 * (k - 1)) * 9 = (3 : ℝ) ^ k * (3 : ℝ) ^ k := by
    have hz : (3 : ℝ) ^ (2 * (k - 1) + 2) =
        (3 : ℝ) ^ (2 * (k - 1)) * (3 : ℝ) ^ (2 : ℤ) :=
      zpow_add₀ (by norm_num) (2 * (k - 1)) 2
    have hw : (3 : ℝ) ^ (k + k) = (3 : ℝ) ^ k * (3 : ℝ) ^ k :=
      zpow_add₀ (by norm_num) k k
    rw [show (2 : ℤ) * (k - 1) + 2 = k + k by ring, hw,
      show ((3 : ℝ) ^ (2 : ℤ)) = 9 by norm_num] at hz
    exact hz.symm
  have hmax : Support.shellW1InfGradNorm k f ≤
      localCubeSecondDerivNorm k f + (3 : ℝ) ^ (-k) * localCubeDerivNorm k f := by
    rw [Support.shellW1InfGradNorm_def]
    exact max_le (by linarith only [mul_nonneg hnegpos.le hD]) (by linarith only [hS])
  have hcancel : (3 : ℝ) ^ k * (3 : ℝ) ^ k *
        ((3 : ℝ) ^ (-k) * localCubeDerivNorm k f) =
      (3 : ℝ) ^ k * localCubeDerivNorm k f := by
    calc (3 : ℝ) ^ k * (3 : ℝ) ^ k * ((3 : ℝ) ^ (-k) * localCubeDerivNorm k f)
        = ((3 : ℝ) ^ k * (3 : ℝ) ^ (-k)) *
            ((3 : ℝ) ^ k * localCubeDerivNorm k f) := by ring
      _ = (3 : ℝ) ^ k * localCubeDerivNorm k f := by rw [hinv, one_mul]
  have hAD : (0 : ℝ) ≤ (3 : ℝ) ^ k * localCubeDerivNorm k f := mul_nonneg hApos.le hD
  calc Real.rpow 3 (2 * (k : ℝ)) * Support.shellW1InfGradNorm k f
      ≤ (3 : ℝ) ^ (2 * k) *
          (localCubeSecondDerivNorm k f + (3 : ℝ) ^ (-k) * localCubeDerivNorm k f) := by
        rw [rpow_two_mul_eq_zpow]
        exact mul_le_mul_of_nonneg_left hmax h2k.le
    _ = (3 : ℝ) ^ k * (3 : ℝ) ^ k * localCubeSecondDerivNorm k f +
          (3 : ℝ) ^ k * localCubeDerivNorm k f := by
        rw [mul_add, h1, hcancel]
    _ ≤ 3 * ((3 : ℝ) ^ k * localCubeDerivNorm k f) +
          (3 : ℝ) ^ k * (3 : ℝ) ^ k * localCubeSecondDerivNorm k f := by
        linarith only [hAD]
    _ = 9 * largeCubeDerivGauge k (k - 1) f := by
        rw [largeCubeDerivGauge, ← h3, ← h2]
        ring

/-! ## 2. The `Γ₂` display of the bottom layer -/

/-- The explicit constant of the bottom-layer display: `9` times the proved
`e.W1inf.jL.bound.smaller` constant. -/
def bottomGradConst (d : ℕ) : ℝ := 9 * shellW1InfSmallerConst d

theorem bottomGradConst_nonneg (d : ℕ) : 0 ≤ bottomGradConst d :=
  mul_nonneg (by norm_num) (shellW1InfSmallerConst_nonneg d)

/-- `3^{2j} ‖∇ j_{j−1}‖_{W^{1,∞}(3^j v + □_j)} = 𝒪_{Γ₂}(C(d) 3^{γ j})`, with the
explicit constant `C(d) = 9 · shellW1InfSmallerConst d`.  No exponent is moved:
the proved translated display is read at cube scale `j`, shell scale `j − 1`,
so its `(l − k)^{1/2}` factor is `1` and its amplitude `3^{γ(j−1)}` is at most
the target `3^{γ j}`. -/
theorem isBigOWith_gammaSigma_weightedBottomGradLayer (M : ABKModel d) (k : ℤ)
    (v : Fin d → ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k - 1))
      (bottomGradConst d * Real.rpow 3 (M.gamma * (k : ℝ))) := by
  have hbase := isBigOWith_gammaSigma_largeCubeDerivGauge_lt_translate M
    (l := k) (k := k - 1) (by omega) (Support.triadicLatticePoint k v)
  have hcut := isBigOWith_cutoffSampleLaw_comp_val (M := M) hbase
  have hstep := (IsBigOWith.const_mul (by norm_num : (0 : ℝ) ≤ 9) hcut).of_le
    (fun omega : Cutoff.CutoffSample d =>
      rpow_weighted_shellW1InfGradNorm_le_largeCubeDerivGauge k
        (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 (k - 1))))
  refine hstep.mono_scale ?_
  have hsqrt : Real.sqrt ((k : ℝ) - (((k - 1 : ℤ)) : ℝ)) = 1 := by
    rw [show (k : ℝ) - (((k - 1 : ℤ)) : ℝ) = 1 by push_cast; ring, Real.sqrt_one]
  have hamp : Real.rpow 3 (M.gamma * (((k - 1 : ℤ)) : ℝ)) ≤
      Real.rpow 3 (M.gamma * (k : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkk : (((k - 1 : ℤ)) : ℝ) ≤ (k : ℝ) := by push_cast; linarith only []
    exact mul_le_mul_of_nonneg_left hkk M.shellPrefix.gamma_pos.le
  have hC : (0 : ℝ) ≤ 9 * shellW1InfSmallerConst d :=
    mul_nonneg (by norm_num) (shellW1InfSmallerConst_nonneg d)
  calc (9 : ℝ) * (shellW1InfSmallerConst d * Real.sqrt ((k : ℝ) - (((k - 1 : ℤ)) : ℝ)) *
          Real.rpow 3 (M.gamma * (((k - 1 : ℤ)) : ℝ)))
      = (9 * shellW1InfSmallerConst d) *
          Real.rpow 3 (M.gamma * (((k - 1 : ℤ)) : ℝ)) := by
        rw [hsqrt]; ring
    _ ≤ (9 * shellW1InfSmallerConst d) * Real.rpow 3 (M.gamma * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hamp hC
    _ = bottomGradConst d * Real.rpow 3 (M.gamma * (k : ℝ)) := by
        rw [bottomGradConst]

/-! ## 3. The whole `L`-free gradient slot as one series -/

/-- The full layer series of the gradient slot at the cube `3^k v + □_k`: the
bottom layer `i = k − 1` together with the whole deep block. -/
def fullGradSeries (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑' n : ℕ, gradLayerGauge k v omega (k - 1 + (n : ℤ))

/-- The geometric part of the full-slot constant. -/
def fullGradBase (M : ABKModel d) : ℝ :=
  (bottomGradConst d + 3) * (1 - Real.rpow 3 (M.gamma - 1))⁻¹

/-- The explicit constant of the full-slot display. -/
def fullGradConst (M : ABKModel d) : ℝ := gammaTriangleConst 2 * fullGradBase M

theorem fullGradBase_pos (M : ABKModel d) : 0 < fullGradBase M := by
  have h1 : Real.rpow 3 (M.gamma - 1) < 1 := rpow_gamma_sub_one_lt_one M
  have h2 : (0 : ℝ) < 1 - Real.rpow 3 (M.gamma - 1) := by linarith only [h1]
  have h3 : (0 : ℝ) ≤ bottomGradConst d := bottomGradConst_nonneg d
  unfold fullGradBase
  positivity

theorem fullGradConst_pos (M : ABKModel d) : 0 < fullGradConst M :=
  mul_pos (gammaTriangleConst_pos (σ := (2 : ℝ))) (fullGradBase_pos M)

/-- The amplitude family of the full series: geometric with ratio `3^{γ−1}`. -/
def fullGradAmp (M : ABKModel d) (k : ℤ) (n : ℕ) : ℝ :=
  (bottomGradConst d + 3) * Real.rpow 3 (M.gamma * (k : ℝ)) *
    Real.rpow 3 (M.gamma - 1) ^ n

private theorem fullGradAmp_pos (M : ABKModel d) (k : ℤ) (n : ℕ) :
    0 < fullGradAmp M k n := by
  have h3 : (0 : ℝ) ≤ bottomGradConst d := bottomGradConst_nonneg d
  have hr : (0 : ℝ) < Real.rpow 3 (M.gamma - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hk : (0 : ℝ) < Real.rpow 3 (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold fullGradAmp
  positivity

private theorem summable_fullGradAmp (M : ABKModel d) (k : ℤ) :
    Summable (fullGradAmp M k) :=
  (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
    (rpow_gamma_sub_one_lt_one M)).mul_left _

private theorem tsum_fullGradAmp (M : ABKModel d) (k : ℤ) :
    ∑' n : ℕ, fullGradAmp M k n =
      fullGradBase M * Real.rpow 3 (M.gamma * (k : ℝ)) := by
  have hgeo : ∑' n : ℕ, Real.rpow 3 (M.gamma - 1) ^ n =
      (1 - Real.rpow 3 (M.gamma - 1))⁻¹ :=
    tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (rpow_gamma_sub_one_lt_one M)
  unfold fullGradAmp fullGradBase
  rw [tsum_mul_left, hgeo]
  ring

/-- The per-layer display of the full series, at the geometric amplitude. -/
private theorem isBigOWith_gammaSigma_fullGradLayer (M : ABKModel d) (k : ℤ)
    (v : Fin d → ℤ) (n : ℕ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k - 1 + (n : ℤ)))
      (fullGradAmp M k n) := by
  have hkpos : (0 : ℝ) < Real.rpow 3 (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrpos : (0 : ℝ) < Real.rpow 3 (M.gamma - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hB : (0 : ℝ) ≤ bottomGradConst d := bottomGradConst_nonneg d
  cases n with
  | zero =>
      have h := isBigOWith_gammaSigma_weightedBottomGradLayer M k v
      rw [show k - 1 + ((0 : ℕ) : ℤ) = k - 1 by push_cast; ring]
      refine h.mono_scale ?_
      have hpow : Real.rpow 3 (M.gamma - 1) ^ (0 : ℕ) = 1 := pow_zero _
      unfold fullGradAmp
      rw [hpow, mul_one]
      have : bottomGradConst d ≤ bottomGradConst d + 3 := by linarith only []
      exact mul_le_mul_of_nonneg_right this hkpos.le
  | succ n' =>
      have hki : k ≤ k + (n' : ℤ) := by omega
      have h := isBigOWith_gammaSigma_weightedGradLayer M hki v
      rw [show k - 1 + ((n' + 1 : ℕ) : ℤ) = k + (n' : ℤ) by push_cast; ring]
      refine h.mono_scale ?_
      -- the proved layer amplitude is `3^{γk} r^{n'}`; the family is `C 3^{γk} r^{n'+1}`
      have hsplit : Real.rpow 3 ((k : ℝ) + (M.gamma - 1) * (((k + (n' : ℤ) : ℤ)) : ℝ)) =
          Real.rpow 3 (M.gamma * (k : ℝ)) * Real.rpow 3 (M.gamma - 1) ^ n' := by
        have hcast : (((k + (n' : ℤ) : ℤ)) : ℝ) = (k : ℝ) + (n' : ℝ) := by
          push_cast; ring
        rw [hcast,
          show (k : ℝ) + (M.gamma - 1) * ((k : ℝ) + (n' : ℝ)) =
            M.gamma * (k : ℝ) + (M.gamma - 1) * (n' : ℝ) by ring,
          rpow3_add, rpow3_mul_natCast]
      have hrge : (1 : ℝ) ≤ 3 * Real.rpow 3 (M.gamma - 1) := by
        have hmono : Real.rpow 3 (-1 : ℝ) ≤ Real.rpow 3 (M.gamma - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith only [M.shellPrefix.gamma_pos])
        have hval : (3 : ℝ) * Real.rpow 3 (-1 : ℝ) = 1 := by
          have hadd : Real.rpow 3 ((1 : ℝ) + (-1 : ℝ)) =
              Real.rpow 3 (1 : ℝ) * Real.rpow 3 (-1 : ℝ) := rpow3_add 1 (-1)
          rw [show (1 : ℝ) + (-1 : ℝ) = 0 by norm_num,
            show Real.rpow 3 (0 : ℝ) = 1 from Real.rpow_zero 3,
            show Real.rpow 3 (1 : ℝ) = 3 from Real.rpow_one 3] at hadd
          exact hadd.symm
        have hscaled : (3 : ℝ) * Real.rpow 3 (-1 : ℝ) ≤
            3 * Real.rpow 3 (M.gamma - 1) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
        linarith only [hval, hscaled]
      have hfac : (1 : ℝ) ≤ (bottomGradConst d + 3) * Real.rpow 3 (M.gamma - 1) := by
        have hmul : 3 * Real.rpow 3 (M.gamma - 1) ≤
            (bottomGradConst d + 3) * Real.rpow 3 (M.gamma - 1) :=
          mul_le_mul_of_nonneg_right (by linarith only [hB]) hrpos.le
        linarith only [hrge, hmul]
      have hbase : (0 : ℝ) ≤ Real.rpow 3 (M.gamma * (k : ℝ)) *
          Real.rpow 3 (M.gamma - 1) ^ n' :=
        mul_nonneg hkpos.le (pow_nonneg hrpos.le n')
      unfold fullGradAmp
      calc Real.rpow 3 ((k : ℝ) + (M.gamma - 1) * (((k + (n' : ℤ) : ℤ)) : ℝ))
          = 1 * (Real.rpow 3 (M.gamma * (k : ℝ)) *
              Real.rpow 3 (M.gamma - 1) ^ n') := by rw [hsplit, one_mul]
        _ ≤ ((bottomGradConst d + 3) * Real.rpow 3 (M.gamma - 1)) *
              (Real.rpow 3 (M.gamma * (k : ℝ)) *
                Real.rpow 3 (M.gamma - 1) ^ n') :=
            mul_le_mul_of_nonneg_right hfac hbase
        _ = (bottomGradConst d + 3) * Real.rpow 3 (M.gamma * (k : ℝ)) *
              Real.rpow 3 (M.gamma - 1) ^ (n' + 1) := by
            rw [pow_succ]
            ring

/-- **B6, first half, complete: the whole `L`-free gradient slot has the Step-4
target shape.**

`3^{2j} Σ_{i ≥ j−1} ‖∇ j_i‖_{W^{1,∞}(3^j v + □_j)} = 𝒪_{Γ₂}(^{γ j})`, with the
explicit constant `C = (9 · shellW1InfSmallerConst d + 3)(1 − 3^{γ−1})^{-1}`.
No exponent is moved. -/
theorem isBigOWith_gammaSigma_weightedFullGradSeries (M : ABKModel d) (k : ℤ)
    (v : Fin d → ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * fullGradSeries k v omega)
      (fullGradConst M * Real.rpow 3 (M.gamma * (k : ℝ))) := by
  have hbase := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (σ := 2)
    (X := fun (n : ℕ) (omega : Cutoff.CutoffSample d) =>
      Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k - 1 + (n : ℤ)))
    (a := fullGradAmp M k)
    (by norm_num)
    (fun n omega => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (gradLayerGauge_nonneg _ _ _ _))
    (fun n => (measurable_gradLayerGauge k v (k - 1 + (n : ℤ))).const_mul _)
    (fullGradAmp_pos M k) (summable_fullGradAmp M k)
    (isBigOWith_gammaSigma_fullGradLayer M k v) (le_of_eq (tsum_fullGradAmp M k))
  have hfun : (fun omega : Cutoff.CutoffSample d => ∑' n : ℕ,
      Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k - 1 + (n : ℤ))) =
      fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * fullGradSeries k v omega := by
    funext omega
    rw [tsum_mul_left, fullGradSeries]
  rw [hfun] at hbase
  refine hbase.mono_scale (le_of_eq ?_)
  unfold fullGradConst
  ring

/-! ## 4. Identification of the series with the slot -/

/-- Local re-derivation of the `private` `tsum_deepGradTerm_eq` of
`GradSlotMoment.lean`: the `ℕ`-indexed reading of the deep block. -/
theorem tsum_natShift_gradLayerGauge_eq_deepGradSeries (k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) :
    ∑' n : ℕ, gradLayerGauge k v omega (k + (n : ℤ)) = deepGradSeries k v omega := by
  have hinj : Function.Injective fun n : ℕ => k + (n : ℤ) := by
    intro a b hab
    have hab' : k + (a : ℤ) = k + (b : ℤ) := hab
    omega
  have hsupp : Function.support (deepGradTerm k v omega) ⊆
      Set.range fun n : ℕ => k + (n : ℤ) := by
    intro x hx
    have hkx : k ≤ x := by
      by_contra hcon
      exact hx (by rw [deepGradTerm, ite_eq_right hcon])
    exact ⟨(x - k).toNat, by change k + (((x - k).toNat : ℕ) : ℤ) = x; omega⟩
  refine Eq.trans (tsum_congr fun n => ?_) (hinj.tsum_eq hsupp)
  rw [deepGradTerm, ite_eq_left (by omega : k ≤ k + (n : ℤ))]

/-- Where the deep block is summable, the full series really is the bottom layer
plus the deep block. -/
theorem fullGradSeries_eq_of_summable (k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (hsum : Summable (deepGradTerm k v omega)) :
    fullGradSeries k v omega =
      gradLayerGauge k v omega (k - 1) + deepGradSeries k v omega := by
  have hdeepNat : Summable fun n : ℕ => gradLayerGauge k v omega (k + (n : ℤ)) := by
    have hinj : Function.Injective fun n : ℕ => k + (n : ℤ) := by
      intro a b hab
      have hab' : k + (a : ℤ) = k + (b : ℤ) := hab
      omega
    refine (hsum.comp_injective hinj).congr fun n => ?_
    change deepGradTerm k v omega (k + (n : ℤ)) = gradLayerGauge k v omega (k + (n : ℤ))
    rw [deepGradTerm, ite_eq_left (by omega : k ≤ k + (n : ℤ))]
  have hshift : Summable fun n : ℕ => gradLayerGauge k v omega (k - 1 + (n : ℤ)) := by
    refine (summable_nat_add_iff (f := fun n : ℕ =>
      gradLayerGauge k v omega (k - 1 + (n : ℤ))) 1).mp ?_
    refine hdeepNat.congr fun n => ?_
    rw [show k - 1 + ((n + 1 : ℕ) : ℤ) = k + (n : ℤ) by push_cast; ring]
  rw [fullGradSeries, hshift.tsum_eq_zero_add]
  have hhead : gradLayerGauge k v omega (k - 1 + ((0 : ℕ) : ℤ)) =
      gradLayerGauge k v omega (k - 1) := by
    rw [show k - 1 + ((0 : ℕ) : ℤ) = k - 1 by push_cast; ring]
  have htail : (∑' n : ℕ, gradLayerGauge k v omega (k - 1 + ((n + 1 : ℕ) : ℤ))) =
      deepGradSeries k v omega := by
    rw [← tsum_natShift_gradLayerGauge_eq_deepGradSeries k v omega]
    exact tsum_congr fun n => by
      rw [show k - 1 + ((n + 1 : ℕ) : ℤ) = k + (n : ℤ) by push_cast; ring]
  rw [hhead, htail]

/-- **The `L`-free gradient slot equals the weighted full series, almost surely.**

Combined with `isBigOWith_gammaSigma_weightedFullGradSeries` this is the Step-4
target shape `𝒪_{Γ₂}(^{γ j})` for the whole slot. -/
theorem ae_lFreeGradSlot_eq_weighted_fullGradSeries (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (hkm : R.scale ≤ m) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lFreeGradSlot m (tailSeriesGauge m) R omega =
        Real.rpow 3 (2 * (R.scale : ℝ)) * fullGradSeries R.scale R.index omega := by
  filter_upwards [ae_forall_summable_tailLayerTerm M m,
    ae_lFreeGradSlot_eq_bottomLayer_add_deep M m R hkm] with omega hsum hslot
  have hmid : Summable fun i : ℤ =>
      (if R.scale ≤ i ∧ i ≤ m then gradLayerGauge R.scale R.index omega i else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc R.scale m) fun i hi => ?_
    rw [ite_eq_right (fun h => hi (Finset.mem_Icc.mpr h))]
  have hdeep : Summable (deepGradTerm R.scale R.index omega) :=
    ((hsum R.scale R.index).add hmid).congr fun i =>
      (deepGradTerm_eq_add m R.scale R.index omega hkm i).symm
  rw [hslot, fullGradSeries_eq_of_summable R.scale R.index omega hdeep]
  ring

end

end Algsuperdiff.Section4.Provider.BoundsEaL
