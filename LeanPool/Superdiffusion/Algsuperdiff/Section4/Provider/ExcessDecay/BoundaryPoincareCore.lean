/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.MatchedPair.ScaledPoincare

/-!
# BoundaryPoincareCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The zero-set Poincaré inequality on an axis cube

This is the analytic core of the funded unit: a **coefficient-free** Poincaré
inequality for an `H¹` function that vanishes on a subset of the cube whose
volume is a definite fraction of the cube's.

```text
  ‖u‖_{L²(A)} ≤ (1 + √K) · C(d) · L · Σᵢ ‖∂ᵢu‖_{L²(A)}
      whenever  u = 0 on E ⊆ A  and  |A| ≤ K |E| ,   A = axisCube z L .
```

The proof is the classical two-line argument on top of the **mean-zero**
Poincaré inequality (CoarseGraining's `scaled_meanZero_poincare`, whose
constant `unitMeanZeroPoincareConst d · L` is the absolute constant of the
fixed unit corner cube times the side): the mean is read off on `E`, where `u`
vanishes, so `|E|^{1/2} |(u)_A| = ‖u - (u)_A‖_{L²(E)} ≤ ‖u - (u)_A‖_{L²(A)}`,
and the triangle inequality then pays `(1 + (|A|/|E|)^{1/2})`.

This is the *trace-measure* half of the boundary Poincaré in the only sense the
development's carriers support: no surface measure exists anywhere in
CoarseGraining or Mathlib, and none is needed — the boundary datum enters
through the **volume** of the part of the cube lying outside the domain, where
the zero extension of an `H¹₀` function vanishes identically.  See
`BoundaryTraceMeasure` for that extension and for the geometric input `|A| ≤
3 |E|`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- CoarseGraining's domain measure is the restricted volume.  (Definitional;
recorded so the `MemLp` fields of an `H1Function` can be used against
`volumeMeasureOn`.) -/
private theorem volumeMeasureOn_eq_restrict (U : Set (Vec d)) :
    volumeMeasureOn U = volume.restrict U := rfl

/-- The mean of `u` over `A`, weighted by the square root of the volume of a
subset on which `u` vanishes, is at most the mean-zero `L²` norm. -/
private theorem enorm_average_mul_le {A E : Set (Vec d)} (u : Vec d → ℝ)
    (hEsub : E ⊆ A) (hEmeas : MeasurableSet E) (hE0 : volume E ≠ 0) {a : ℝ}
    (hzero : ∀ y ∈ E, u y = 0) :
    ‖a‖ₑ * volume E ^ (1 / 2 : ℝ) ≤
      eLpNorm (fun x => u x - a) 2 (volume.restrict A) := by
  have hrestr : (volume.restrict E) ≠ 0 := by
    intro h
    exact hE0 (by simpa using congrArg (fun μ => μ E) h)
  have hae : (fun x => u x - a) =ᵐ[volume.restrict E] (fun _ => -a) := by
    refine (MeasureTheory.ae_restrict_iff' hEmeas).2 ?_
    filter_upwards with x hx
    rw [hzero x hx, zero_sub]
  have hcongr : eLpNorm (fun x => u x - a) 2 (volume.restrict E) =
      eLpNorm (fun _ : Vec d => -a) 2 (volume.restrict E) := eLpNorm_congr_ae hae
  have hconst : eLpNorm (fun _ : Vec d => -a) 2 (volume.restrict E) =
      ‖a‖ₑ * volume E ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_const (-a) (by norm_num) hrestr, Measure.restrict_apply_univ,
      enorm_neg]
    norm_num
  have hmono : eLpNorm (fun x => u x - a) 2 (volume.restrict E) ≤
      eLpNorm (fun x => u x - a) 2 (volume.restrict A) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hEsub le_rfl)
  rw [← hconst, ← hcongr]
  exact hmono

/-- **The zero-set Poincaré, conditional on a supplied mean-zero bound.**

Private and conditional (`hmeanZero` is the caller's input), as the name
discloses; the unconditional axis-cube instance is
`eLpNorm_le_of_zeroSet_of_volume_le`. -/
private theorem eLpNorm_le_of_zeroSet_of_meanZeroBound {U E : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {K C S : ℝ} (u : H1Function U)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S) (hEsub : E ⊆ U)
    (hEmeas : MeasurableSet E) (hzero : ∀ y ∈ E, u.toFun y = 0)
    (hvol : volume U ≤ ENNReal.ofReal K * volume E)
    (hmeanZero : (eLpNorm u.subAverage.toFun 2 (volumeMeasureOn U)).toReal ≤
      C * S) :
    (eLpNorm u.toFun 2 (volumeMeasureOn U)).toReal ≤ (1 + Real.sqrt K) * C * S := by
  classical
  have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hone : 0 ≤ 1 + Real.sqrt K := by linarith only [hsqrtK]
  have hsubfun : u.subAverage.toFun =
      fun x => u.toFun x - integralAverage U u.toFun := by
    funext x
    exact H1Function.subAverage_apply u x
  rw [hsubfun] at hmeanZero
  by_cases hU0 : volume U = 0
  · have hzeroμ : volumeMeasureOn U = 0 := by
      rw [volumeMeasureOn_eq_restrict]
      exact Measure.restrict_eq_zero.2 hU0
    rw [hzeroμ, eLpNorm_measure_zero, ENNReal.toReal_zero]
    exact mul_nonneg (mul_nonneg hone hC) hS
  · have hE0 : volume E ≠ 0 := by
      intro h
      exact hU0 (le_antisymm (by simpa [h] using hvol) zero_le)
    have hrestrU : (volume.restrict U) ≠ 0 := by
      intro h
      exact hU0 (by simpa using congrArg (fun μ => μ U) h)
    have hmem : MemLp (fun x => u.toFun x - integralAverage U u.toFun) 2
        (volume.restrict U) := by
      have := u.subAverage.memL2
      rwa [hsubfun] at this
    have hNtop : eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
        (volume.restrict U) ≠ ⊤ := hmem.eLpNorm_lt_top.ne
    have hmean := enorm_average_mul_le (A := U) (E := E) u.toFun hEsub hEmeas hE0
      (a := integralAverage U u.toFun) hzero
    have hratio : volume U ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt K) * volume E ^ (1 / 2 : ℝ) := by
      have h1 : volume U ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal K * volume E) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hvol (by norm_num)
      rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hK (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow] at h1
    have hbig : ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt K) *
          eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) := by
      calc ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ)
          ≤ ‖integralAverage U u.toFun‖ₑ *
              (ENNReal.ofReal (Real.sqrt K) * volume E ^ (1 / 2 : ℝ)) :=
            mul_le_mul' le_rfl hratio
        _ = ENNReal.ofReal (Real.sqrt K) *
              (‖integralAverage U u.toFun‖ₑ * volume E ^ (1 / 2 : ℝ)) := by ring
        _ ≤ ENNReal.ofReal (Real.sqrt K) *
              eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
                (volume.restrict U) := mul_le_mul' le_rfl hmean
    have hconstU : eLpNorm (fun _ : Vec d => integralAverage U u.toFun) 2
        (volume.restrict U) =
        ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_const _ (by norm_num) hrestrU, Measure.restrict_apply_univ]
      norm_num
    have htri : eLpNorm u.toFun 2 (volume.restrict U) ≤
        eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) +
          ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) := by
      have hadd := eLpNorm_add_le (p := 2) (μ := volume.restrict U)
        (f := fun x => u.toFun x - integralAverage U u.toFun)
        (g := fun _ : Vec d => integralAverage U u.toFun) (by norm_num)
      rw [hconstU] at hadd
      calc eLpNorm u.toFun 2 (volume.restrict U)
          = eLpNorm ((fun x => u.toFun x - integralAverage U u.toFun) +
              (fun _ : Vec d => integralAverage U u.toFun)) 2
              (volume.restrict U) := by
            congr 1
            funext x
            simp
        _ ≤ _ := hadd
    have hchain : eLpNorm u.toFun 2 (volume.restrict U) ≤
        (1 + ENNReal.ofReal (Real.sqrt K)) *
          eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) := by
      refine htri.trans ?_
      rw [add_mul, one_mul]
      exact add_le_add le_rfl hbig
    have hRtop : (1 + ENNReal.ofReal (Real.sqrt K)) *
        eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
          (volume.restrict U) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩) hNtop
    have hreal : (eLpNorm u.toFun 2 (volume.restrict U)).toReal ≤
        (1 + Real.sqrt K) *
          (eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U)).toReal := by
      have h := ENNReal.toReal_mono hRtop hchain
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.one_ne_top
        ENNReal.ofReal_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_ofReal hsqrtK] at h
    rw [volumeMeasureOn_eq_restrict]
    refine hreal.trans ?_
    rw [volumeMeasureOn_eq_restrict] at hmeanZero
    calc (1 + Real.sqrt K) *
          (eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U)).toReal
        ≤ (1 + Real.sqrt K) * (C * S) :=
          mul_le_mul_of_nonneg_left hmeanZero hone
      _ = (1 + Real.sqrt K) * C * S := by ring

/-- **The zero-set Poincaré inequality on an axis cube.**

An `H¹` function on `axisCube z L` that vanishes on a measurable subset `E`
carrying at least a `K⁻¹` fraction of the cube's volume obeys the
*un-subtracted* `L²` Poincaré inequality at the cube's own scale, with the
coefficient-free constant `(1 + √K) · C(d) · L`. -/
theorem eLpNorm_le_of_zeroSet_of_volume_le (z : Vec d) {L K : ℝ} (hL : 0 < L)
    (hK : 0 ≤ K) (u : H1Function (axisCube z L)) {E : Set (Vec d)}
    (hEsub : E ⊆ axisCube z L) (hEmeas : MeasurableSet E)
    (hzero : ∀ y ∈ E, u.toFun y = 0)
    (hvol : volume (axisCube z L) ≤ ENNReal.ofReal K * volume E) :
    (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal ≤
      (1 + Real.sqrt K) * (unitMeanZeroPoincareConst d * L) *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2
            (volumeMeasureOn (axisCube z L))).toReal := by
  refine eLpNorm_le_of_zeroSet_of_meanZeroBound (K := K)
    (C := unitMeanZeroPoincareConst d * L)
    (S := ∑ i : Fin d,
      (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
    u hK (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hL.le)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) hEsub hEmeas hzero hvol ?_
  exact scaled_meanZero_poincare (d := d) z hL u

end

end Algsuperdiff.Section4.Provider.ExcessDecay
