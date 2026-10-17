/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GaussianMaximum

/-!
# ShellBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The single-shell stream bounds of ABK26

This module proves the first two displays in the proof of ABK26's stream
increment lemma: the value bound `e.jk.O` and the derivative bound
`e.nabla.jk.O`.  Both are obtained from the frozen assumption (J2) transported
through the frozen marginal scaling law `e.diff.law.shift`, exactly as in the
source.

The two source displays are, for every `k ∈ ℤ`,

* `‖j_k‖_{L∞(cu_k)} = O_{Γ₂}(3^{γk})` (ABK26), and
* `‖∇j_k‖_{L∞(cu_k)} + 3^k ‖∇²j_k‖_{L∞(cu_k)} = O_{Γ₂}(^{(γ-1)k})`
  (ABK26).

Here `‖j_k‖_{L∞(cu_k)}` is `Algsuperdiff.Section3.Cutoff.localCubeControl k`
applied to the shell at index `k`, and the two derivative suprema are
`localCubeDerivNorm k` and `localCubeSecondDerivNorm k`.  The amplitudes below
are the literal source amplitudes with constant `1`: the J2 normalization
`e.kn.reg.ass.with.gamma` (ABK26) weights the derivative terms by `√d ≥ 1` and
`d ≥ 1`, so no dimensional constant is needed.  In particular the conclusions
are at least as strong as the source's `C(d)` form.

## Main results

* `isBigOWith_gammaSigma_localCubeControl_shell`: `e.jk.O`.
* `isBigOWith_gammaSigma_shellDerivGauge`: `e.nabla.jk.O`.
* `isBigOWith_gammaSigma_shellDerivGauge_cube`: the same estimate measured on
  any smaller origin cube `cu_ell` with `ell ≤ k`, which is the form consumed
  by the increment estimate.

## References

* ABK26.
* ABK26, `e.kn.reg.ass.with.gamma`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The J2 tail under the zero-shell marginal law -/

/-- The frozen (J2) Gaussian tail, read under the exact zero-shell marginal
law. -/
theorem zeroShell_j2Observable_gaussian_tail (M : ABKModel d) (t : ℝ) (ht : 1 ≤ t) :
    (ShellField.zeroShellLaw M.P).toMeasure
        {j | t < ShellField.j2Observable d j} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  change Measure.map (fun F : ShellSeq d => F 0) M.P.toMeasure
      {j | t < ShellField.j2Observable d j} ≤ _
  rw [Measure.map_apply_of_aemeasurable
    ShellField.measurable_zeroShellMap.aemeasurable
    (measurableSet_lt measurable_const (ShellField.j2Observable_measurable d))]
  simpa only [Set.preimage_ofPred_eq] using M.J2.gaussian_tail t ht

/-- The J2 observable has a unit-scale `Γ₂` tail under the zero-shell law. -/
theorem isBigOWith_gammaSigma_zeroShell_j2Observable (M : ABKModel d) :
    IndependentSums.IsBigOWith (ShellField.zeroShellLaw M.P).toMeasure
      (IndependentSums.gammaSigma 2) (ShellField.j2Observable d) 1 :=
  Algsuperdiff.Probability.isBigOWith_gammaSigma_two_of_gaussian_tail
    (by simpa only [one_mul, ← Real.rpow_natCast] using!
      zeroShell_j2Observable_gaussian_tail M)

/-- The unit-cube value norm has a unit-scale `Γ₂` tail under the zero-shell
law. -/
theorem isBigOWith_gammaSigma_zeroShell_unitCubeValueNorm (M : ABKModel d) :
    IndependentSums.IsBigOWith (ShellField.zeroShellLaw M.P).toMeasure
      (IndependentSums.gammaSigma 2) ShellField.unitCubeValueNorm 1 :=
  (isBigOWith_gammaSigma_zeroShell_j2Observable M).of_le
    (fun j => unitCubeValueNorm_le_j2Observable j)

/-- In dimension `d ≥ 1` the unweighted sum of the two J2 derivative norms is
dominated by the J2 observable itself, because the source weights `√d` and `d`
are at least one.  This is why the derivative display below carries no
dimensional constant. -/
theorem unitCubeDerivNorm_add_unitCubeSecondDerivNorm_le_j2Observable
    (hd : 1 ≤ d) (j : ShellField d) :
    ShellField.unitCubeDerivNorm j + ShellField.unitCubeSecondDerivNorm j ≤
      ShellField.j2Observable d j := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hd1
  have hexpand : ShellField.j2Observable d j =
      ShellField.unitCubeValueNorm j + Real.sqrt d * ShellField.unitCubeDerivNorm j +
        (d : ℝ) * ShellField.unitCubeSecondDerivNorm j := rfl
  have h1 : ShellField.unitCubeDerivNorm j ≤
      Real.sqrt d * ShellField.unitCubeDerivNorm j :=
    le_mul_of_one_le_left (ShellField.unitCubeDerivNorm_nonneg j) hsqrt
  have h2 : ShellField.unitCubeSecondDerivNorm j ≤
      (d : ℝ) * ShellField.unitCubeSecondDerivNorm j :=
    le_mul_of_one_le_left (ShellField.unitCubeSecondDerivNorm_nonneg j) hd1
  rw [hexpand]
  linarith [ShellField.unitCubeValueNorm_nonneg j]

/-- The unweighted sum of the two J2 derivative norms has a unit-scale `Γ₂`
tail under the zero-shell law. -/
theorem isBigOWith_gammaSigma_zeroShell_unitCubeDerivSum (M : ABKModel d) :
    IndependentSums.IsBigOWith (ShellField.zeroShellLaw M.P).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun j => ShellField.unitCubeDerivNorm j + ShellField.unitCubeSecondDerivNorm j)
      1 :=
  (isBigOWith_gammaSigma_zeroShell_j2Observable M).of_le
    (fun j => unitCubeDerivNorm_add_unitCubeSecondDerivNorm_le_j2Observable
      (le_trans one_le_two M.shellPrefix.dimension) j)

/-! ## `e.jk.O`: the value display -/

/-- ABK26's `e.jk.O`: under the canonical shell-sequence law,
`‖j_k‖_{L∞(cu_k)} ≤ O_{Γ₂}(3^{γk})`.  The amplitude is the source amplitude
with constant `1`. -/
theorem isBigOWith_gammaSigma_localCubeControl_shell (M : ABKModel d) (k : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => localCubeControl k (omega k))
      (Real.rpow 3 (M.gamma * (k : ℝ))) := by
  have hzero : IndependentSums.IsBigOWith (ShellField.zeroShellLaw M.P).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun j => Real.rpow 3 (M.gamma * (k : ℝ)) * ShellField.unitCubeValueNorm j)
      (Real.rpow 3 (M.gamma * (k : ℝ)) * 1) :=
    IndependentSums.IsBigOWith.const_mul (Real.rpow_nonneg (by norm_num) _)
      (isBigOWith_gammaSigma_zeroShell_unitCubeValueNorm M)
  rw [mul_one] at hzero
  refine Algsuperdiff.Probability.isBigOWith_gammaSigma_of_map_eq
    ((measurable_localCubeControl k).comp (measurable_pi_apply k))
    (measurable_const.mul ShellField.unitCubeValueNorm_measurable) ?_ hzero
  rw [map_localCubeControl_shell_eq_zero M k k]
  apply Measure.map_congr
  filter_upwards with j
  rw [sub_self, localCubeControl_zero_eq_unitCubeValueNorm]
  rfl

/-! ## `e.nabla.jk.O`: the derivative display -/

private theorem zpow_three_mul_rpow_sub_two (gamma : ℝ) (k : ℤ) :
    (3 : ℝ) ^ k * Real.rpow 3 ((gamma - 2) * (k : ℝ)) =
      Real.rpow 3 ((gamma - 1) * (k : ℝ)) := by
  change (3 : ℝ) ^ k * (3 : ℝ) ^ ((gamma - 2) * (k : ℝ)) =
    (3 : ℝ) ^ ((gamma - 1) * (k : ℝ))
  rw [← Real.rpow_intCast (3 : ℝ) k, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The exact zero-shell form of the derivative gauge after the triadic
scaling action: the two chain-rule factors combine into the single source
amplitude `3^{(γ-1)k}`. -/
private theorem shellDerivGauge_triadicScale (gamma : ℝ) (k : ℤ) (j : ShellField d) :
    localCubeDerivNorm k (ShellField.triadicScale gamma k j) +
        (3 : ℝ) ^ k * localCubeSecondDerivNorm k (ShellField.triadicScale gamma k j) =
      Real.rpow 3 ((gamma - 1) * (k : ℝ)) *
        (ShellField.unitCubeDerivNorm j + ShellField.unitCubeSecondDerivNorm j) := by
  rw [localCubeDerivNorm_triadicScale, localCubeSecondDerivNorm_triadicScale,
    sub_self, localCubeDerivNorm_zero, localCubeSecondDerivNorm_zero,
    show (3 : ℝ) ^ k * (Real.rpow 3 ((gamma - 2) * (k : ℝ)) *
        ShellField.unitCubeSecondDerivNorm j) =
      ((3 : ℝ) ^ k * Real.rpow 3 ((gamma - 2) * (k : ℝ))) *
        ShellField.unitCubeSecondDerivNorm j by ring,
    zpow_three_mul_rpow_sub_two]
  ring

/-- The shell derivative gauge is nonnegative. -/
theorem shellDerivGauge_nonneg (ell : ℤ) (j : ShellField d) :
    0 ≤ localCubeDerivNorm ell j + (3 : ℝ) ^ ell * localCubeSecondDerivNorm ell j :=
  add_nonneg (localCubeDerivNorm_nonneg ell j)
    (mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) ell).le
      (localCubeSecondDerivNorm_nonneg ell j))

theorem measurable_shellDerivGauge (ell : ℤ) :
    Measurable (fun j : ShellField d =>
      localCubeDerivNorm ell j + (3 : ℝ) ^ ell * localCubeSecondDerivNorm ell j) :=
  (measurable_localCubeDerivNorm ell).add
    (measurable_const.mul (measurable_localCubeSecondDerivNorm ell))

/-- ABK26's `e.nabla.jk.O`: under the canonical
shell-sequence law,
`‖∇j_k‖_{L∞(cu_k)} + 3^k ‖∇²j_k‖_{L∞(cu_k)} ≤ O_{Γ₂}(3^{(γ-1)k})`.
The source states the amplitude with a dimensional constant `C(d)`; the exact
J2 normalization gives it with constant `1`. -/
theorem isBigOWith_gammaSigma_shellDerivGauge (M : ABKModel d) (k : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        localCubeDerivNorm k (omega k) +
          (3 : ℝ) ^ k * localCubeSecondDerivNorm k (omega k))
      (Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
  have hzero : IndependentSums.IsBigOWith (ShellField.zeroShellLaw M.P).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun j => Real.rpow 3 ((M.gamma - 1) * (k : ℝ)) *
        (ShellField.unitCubeDerivNorm j + ShellField.unitCubeSecondDerivNorm j))
      (Real.rpow 3 ((M.gamma - 1) * (k : ℝ)) * 1) :=
    IndependentSums.IsBigOWith.const_mul (Real.rpow_nonneg (by norm_num) _)
      (isBigOWith_gammaSigma_zeroShell_unitCubeDerivSum M)
  rw [mul_one] at hzero
  refine Algsuperdiff.Probability.isBigOWith_gammaSigma_of_map_eq
    ((measurable_shellDerivGauge k).comp (measurable_pi_apply k))
    (measurable_const.mul
      (ShellField.unitCubeDerivNorm_measurable.add
        ShellField.unitCubeSecondDerivNorm_measurable)) ?_ hzero
  rw [map_shellObservable_eq_zero_triadicScale M k _ (measurable_shellDerivGauge k)]
  apply Measure.map_congr
  filter_upwards with j
  exact shellDerivGauge_triadicScale M.gamma k j

/-- The derivative display measured on a smaller origin cube.  For `ell ≤ k`
the cube `cu_ell` is contained in `cu_k`, so the shell at index `k` obeys the
same `Γ₂` bound there; this is the form summed in ABK26's
`e.nabla.km.kn.infty`. -/
theorem isBigOWith_gammaSigma_shellDerivGauge_cube (M : ABKModel d) {ell k : ℤ}
    (h : ell ≤ k) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        localCubeDerivNorm ell (omega k) +
          (3 : ℝ) ^ ell * localCubeSecondDerivNorm ell (omega k))
      (Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
  refine (isBigOWith_gammaSigma_shellDerivGauge M k).of_le (fun omega => ?_)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ell := zpow_pos (by norm_num) ell
  have hpow : (3 : ℝ) ^ ell ≤ (3 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) h
  have hsecond : (3 : ℝ) ^ ell * localCubeSecondDerivNorm ell (omega k) ≤
      (3 : ℝ) ^ k * localCubeSecondDerivNorm k (omega k) := by
    calc
      (3 : ℝ) ^ ell * localCubeSecondDerivNorm ell (omega k) ≤
          (3 : ℝ) ^ ell * localCubeSecondDerivNorm k (omega k) :=
        mul_le_mul_of_nonneg_left (localCubeSecondDerivNorm_mono h (omega k)) hpos.le
      _ ≤ (3 : ℝ) ^ k * localCubeSecondDerivNorm k (omega k) :=
        mul_le_mul_of_nonneg_right hpow (localCubeSecondDerivNorm_nonneg k (omega k))
  exact add_le_add (localCubeDerivNorm_mono h (omega k)) hsecond

end

end Algsuperdiff.Section3.Provider.Stream
