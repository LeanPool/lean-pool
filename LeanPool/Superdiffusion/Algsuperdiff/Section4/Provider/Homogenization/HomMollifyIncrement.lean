/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyLipschitz

/-!
# HomMollifyIncrement

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the increment estimate `(I)` and the limit

## What this module proves

The remaining two obligations for the family `W_n = (w ⋆ ψ)_{· + □_n}` of
`HomMollifyLipschitz`:

* **(I)** `|W_n(x) - W_{n-1}(x)| ≤ 2 d A · 3^{n(1-s)}`
  (`abs_boxRegularization_sub_pred_le`).  The proof is the *commuting square*
  of the two sliding averages: `(W_n)_{x+□_{n-1}} = (W_{n-1})_{x+□_n}`
  (`boxAverage_boxRegularization_comm`, associativity and commutativity of
  the convolution), so both `W_n` and `W_{n-1}` are within one Lipschitz
  displacement of the same quantity, and `(L)` closes the estimate.  No new
  analytic input is needed: `(I)` is a *consequence* of `(L)`.

* **(hLim)** `W_{n-k}(x) → (w ⋆ ψ)(x)` as `k → ∞`, for every `x`
  (`tendsto_boxRegularization_atTop`).  The mollification `w ⋆ ψ` is smooth,
  so its sliding averages converge to it everywhere by continuity — no
  Lebesgue differentiation is required.

Both are unconditional given the frame of `HomMollifyLipschitz`.

## The constant

`(L)` runs at `d A` and `(I)` at `d A (3^{-1}/2 + 3^{s}/2) ≤ d A (1/6 + 1) ≤ 2
d A` on `0 < s ≤ 1/2`, so both obligations hold at the common constant `2 d A`,
which is what the `holderSeminormBoundOn_of_increments` consumes: the Hölder
constant is `8 · (2 d A) = 16 d A`.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport

open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Elementary box-average identities -/

theorem boxAverage_const (n : ℤ) (x : Vec d) (c : ℝ) :
    boxAverage n x (fun _ => c) = c := by
  rw [boxAverage_eq_inv_mul_integral, setIntegral_const, measureReal_def,
    toReal_volume_boxSet, smul_eq_mul]
  field_simp

theorem boxAverage_sub_const {n : ℤ} {x : Vec d} {f : Vec d → ℝ} (c : ℝ)
    (hf : IntegrableOn f (boxSet n x) volume) :
    boxAverage n x (fun y => f y - c) = boxAverage n x f - c := by
  have hsub : ∫ y in boxSet n x, (f y - c) = (∫ y in boxSet n x, f y) - ∫ _y in boxSet n x, c :=
    integral_sub hf (integrableOn_const (by rw [volume_boxSet]; exact ENNReal.ofReal_ne_top))
  rw [boxAverage_eq_inv_mul_integral, hsub, mul_sub, ← boxAverage_eq_inv_mul_integral,
    ← boxAverage_eq_inv_mul_integral, boxAverage_const]

/-- **A Lipschitz function is within `Lip · 3^n/2` of its scale-`n` box
average.** -/
theorem abs_boxAverage_sub_self_le {n : ℤ} {x : Vec d} {f : Vec d → ℝ} {Lip : ℝ}
    (hLip : 0 ≤ Lip) (hf : IntegrableOn f (boxSet n x) volume)
    (hlip : ∀ a b : Vec d, |f a - f b| ≤ Lip * ‖a - b‖) :
    |boxAverage n x f - f x| ≤ Lip * boxRadius n := by
  have hrw : boxAverage n x f - f x = boxAverage n x fun y => f y - f x :=
    (boxAverage_sub_const (f x) hf).symm
  rw [hrw]
  refine abs_boxAverage_le ?_
  intro y hy
  exact (hlip y x).trans (mul_le_mul_of_nonneg_left (mem_boxSet_iff.1 hy) hLip)

/-! ## 2. The commuting square of two sliding averages -/

theorem boxKernel_norm_le (n : ℤ) (t : Vec d) :
    ‖boxKernel n t‖ ≤ (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ := by
  rw [Real.norm_eq_abs]
  by_cases ht : t ∈ boxSet n 0
  · rw [boxKernel_apply_of_mem ht, abs_of_nonneg (inv_nonneg.mpr (boxVolume_pos n).le)]
  · rw [boxKernel_apply_of_not_mem ht, abs_zero]
    exact (inv_nonneg.mpr (boxVolume_pos n).le)

/-- **The commuting square.**  The scale-`k` average of the scale-`n`
regularization equals the scale-`n` average of the scale-`k` regularization:
the two sliding averages commute. -/
theorem boxAverage_boxRegularization_comm {w ψ : Vec d → ℝ}
    (hwI : Integrable w volume) (hψ : IsMollifierDensity ψ) (n k : ℤ) (x : Vec d) :
    boxAverage k x (boxRegularization n ψ w) = boxAverage n x (boxRegularization k ψ w) := by
  have hU : Integrable (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) volume :=
    hwI.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hψ.integrable
  have hKn : Integrable (boxKernel (d := d) n) volume := integrable_boxKernel n
  have hKk : Integrable (boxKernel (d := d) k) volume := integrable_boxKernel k
  have hassoc1 := convolution_assoc_real (f := boxKernel (d := d) k) (g := boxKernel (d := d) n)
    (k := w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) hKk hKn hU (boxKernel_norm_le k) x
  have hassoc2 := convolution_assoc_real (f := boxKernel (d := d) n) (g := boxKernel (d := d) k)
    (k := w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) hKn hKk hU (boxKernel_norm_le n) x
  calc boxAverage k x (boxRegularization n ψ w)
      = (boxKernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)) x := by
        rw [← convolution_boxKernel_eq_boxAverage, boxRegularization_eq_convolution]
    _ = ((boxKernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel n)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)) x := hassoc1.symm
    _ = ((boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] boxKernel k)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)) x := by
        rw [convolution_comm_real (boxKernel (d := d) k) (boxKernel (d := d) n)]
    _ = (boxKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          boxKernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)) x := hassoc2
    _ = boxAverage n x (boxRegularization k ψ w) := by
        rw [← convolution_boxKernel_eq_boxAverage, boxRegularization_eq_convolution]

/-! ## 3. Continuity and integrability of the regularization -/

theorem continuous_boxRegularization {w ψ : Vec d → ℝ}
    (hwI : Integrable w volume) (hwc : HasCompactSupport w) (hψ : IsMollifierDensity ψ)
    (n : ℤ) : Continuous (boxRegularization n ψ w) :=
  (differentiable_boxRegularization hwI.locallyIntegrable hwc hψ n).continuous

theorem integrableOn_boxRegularization {w ψ : Vec d → ℝ}
    (hwI : Integrable w volume) (hwc : HasCompactSupport w) (hψ : IsMollifierDensity ψ)
    (n k : ℤ) (x : Vec d) :
    IntegrableOn (boxRegularization n ψ w) (boxSet k x) volume :=
  ContinuousOn.integrableOn_compact (isCompact_boxSet k x)
    (continuous_boxRegularization hwI hwc hψ n).continuousOn

/-! ## 4. (I) The increment estimate -/

/-- **(I), the increment obligation.**

Two consecutive regularizations differ by at most `2 d A · 3^{n(1-s)}`.  The
proof uses no analytic input beyond `(L)`: the commuting square places both
`W_n(x)` and `W_{n-1}(x)` within one Lipschitz displacement of the common
quantity `(W_n)_{x+□_{n-1}} = (W_{n-1})_{x+□_n}`. -/
theorem abs_boxRegularization_sub_pred_le {m : ℤ} {s A : ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs2 : s ≤ 1 / 2)
    {ψ : Vec d → ℝ} (hψ : IsMollifierDensity ψ) {n : ℤ} (hn : n ≤ m) (x : Vec d) :
    |boxRegularization n ψ w x - boxRegularization (n - 1) ψ w x|
      ≤ 2 * (d : ℝ) * A * (3 : ℝ) ^ ((n : ℝ) * (1 - s)) := by
  have hP : (0 : ℝ) ≤ (d : ℝ) * A := mul_nonneg (Nat.cast_nonneg d) hgauge.nonneg
  have hB : (0 : ℝ) < (3 : ℝ) ^ ((n : ℝ) * (1 - s)) := three_rpow_pos _
  have hnm1 : n - 1 ≤ m := by omega
  /- the two Lipschitz constan -/
  have hlipn : ∀ a b : Vec d,
      |boxRegularization n ψ w a - boxRegularization n ψ w b|
        ≤ ((d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s))) * ‖a - b‖ := fun a b =>
    abs_boxRegularization_sub_le hw hwI hwc hGI hgauge hψ hn a b
  have hlipn1 : ∀ a b : Vec d,
      |boxRegularization (n - 1) ψ w a - boxRegularization (n - 1) ψ w b|
        ≤ ((d : ℝ) * A * (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s))) * ‖a - b‖ := fun a b =>
    abs_boxRegularization_sub_le hw hwI hwc hGI hgauge hψ hnm1 a b
  have hLn : (0 : ℝ) ≤ (d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s)) :=
    mul_nonneg hP (three_rpow_nonneg _)
  have hLn1 : (0 : ℝ) ≤ (d : ℝ) * A * (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s)) :=
    mul_nonneg hP (three_rpow_nonneg _)
  /- the two displacement boun -/
  have h1 : |boxAverage (n - 1) x (boxRegularization n ψ w) - boxRegularization n ψ w x|
      ≤ ((d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s))) * boxRadius (n - 1) :=
    abs_boxAverage_sub_self_le hLn (integrableOn_boxRegularization hwI hwc hψ n (n - 1) x) hlipn
  have h2 : |boxAverage n x (boxRegularization (n - 1) ψ w) - boxRegularization (n - 1) ψ w x|
      ≤ ((d : ℝ) * A * (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s))) * boxRadius n :=
    abs_boxAverage_sub_self_le hLn1 (integrableOn_boxRegularization hwI hwc hψ (n - 1) n x) hlipn1
  have hcomm : boxAverage (n - 1) x (boxRegularization n ψ w)
      = boxAverage n x (boxRegularization (n - 1) ψ w) :=
    boxAverage_boxRegularization_comm hwI hψ n (n - 1) x
  rw [← hcomm] at h2
  /- the two weights, in the `3^{n(1-s)}` normalizati -/
  have hw1 : (3 : ℝ) ^ (-((n : ℝ) * s)) * boxRadius (n - 1)
      = (3 : ℝ) ^ ((n : ℝ) * (1 - s)) * (1 / 6) := by
    rw [boxRadius_def, ← mul_div_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-((n : ℝ) * s) + (((n - 1 : ℤ)) : ℝ)) = (n : ℝ) * (1 - s) + (-1 : ℝ) by
      push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 by
      rw [Real.rpow_neg_one]; norm_num]
    ring
  have hw2 : (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s)) * boxRadius n
      = (3 : ℝ) ^ ((n : ℝ) * (1 - s)) * ((3 : ℝ) ^ s / 2) := by
    rw [boxRadius_def, ← mul_div_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-((((n - 1 : ℤ)) : ℝ) * s) + (n : ℝ)) = (n : ℝ) * (1 - s) + s by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring
  have h3s : (3 : ℝ) ^ s ≤ 2 := three_rpow_le_two hs2
  /- assemb -/
  have hsplit : |boxRegularization n ψ w x - boxRegularization (n - 1) ψ w x|
      ≤ |boxAverage (n - 1) x (boxRegularization n ψ w) - boxRegularization n ψ w x|
        + |boxAverage (n - 1) x (boxRegularization n ψ w)
            - boxRegularization (n - 1) ψ w x| := by
    calc |boxRegularization n ψ w x - boxRegularization (n - 1) ψ w x|
        ≤ |boxRegularization n ψ w x - boxAverage (n - 1) x (boxRegularization n ψ w)|
          + |boxAverage (n - 1) x (boxRegularization n ψ w)
              - boxRegularization (n - 1) ψ w x| := abs_sub_le _ _ _
      _ = |boxAverage (n - 1) x (boxRegularization n ψ w) - boxRegularization n ψ w x|
          + |boxAverage (n - 1) x (boxRegularization n ψ w)
              - boxRegularization (n - 1) ψ w x| := by
          rw [abs_sub_comm (boxRegularization n ψ w x)
            (boxAverage (n - 1) x (boxRegularization n ψ w))]
  have hterm1 : ((d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s))) * boxRadius (n - 1)
      = (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * (1 / 6)) := by
    rw [mul_assoc, hw1]
  have hterm2 : ((d : ℝ) * A * (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s))) * boxRadius n
      = (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * ((3 : ℝ) ^ s / 2)) := by
    rw [mul_assoc, hw2]
  have hbnd2 : (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * ((3 : ℝ) ^ s / 2))
      ≤ (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1) := by
    refine mul_le_mul_of_nonneg_left ?_ hP
    refine mul_le_mul_of_nonneg_left ?_ hB.le
    linarith only [h3s]
  have hbnd1 : (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * (1 / 6))
      ≤ (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1) := by
    refine mul_le_mul_of_nonneg_left ?_ hP
    refine mul_le_mul_of_nonneg_left ?_ hB.le
    norm_num
  have hfin : (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1)
      + (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1)
      = 2 * (d : ℝ) * A * (3 : ℝ) ^ ((n : ℝ) * (1 - s)) := by ring
  calc |boxRegularization n ψ w x - boxRegularization (n - 1) ψ w x|
      ≤ |boxAverage (n - 1) x (boxRegularization n ψ w) - boxRegularization n ψ w x|
        + |boxAverage (n - 1) x (boxRegularization n ψ w)
            - boxRegularization (n - 1) ψ w x| := hsplit
    _ ≤ ((d : ℝ) * A * (3 : ℝ) ^ (-((n : ℝ) * s))) * boxRadius (n - 1)
        + ((d : ℝ) * A * (3 : ℝ) ^ (-((((n - 1 : ℤ)) : ℝ) * s))) * boxRadius n :=
        add_le_add h1 h2
    _ = (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * (1 / 6))
        + (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * ((3 : ℝ) ^ s / 2)) := by
        rw [hterm1, hterm2]
    _ ≤ (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1)
        + (d : ℝ) * A * ((3 : ℝ) ^ ((n : ℝ) * (1 - s)) * 1) := add_le_add hbnd1 hbnd2
    _ = 2 * (d : ℝ) * A * (3 : ℝ) ^ ((n : ℝ) * (1 - s)) := hfin

/-! ## 5. (hLim) The convergence of the family -/

/-- The box radii shrink to zero as the scale descends. -/
theorem tendsto_boxRadius_atTop (n : ℤ) :
    Filter.Tendsto (fun k : ℕ => boxRadius (n - (k : ℤ))) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun k : ℕ => ((3 : ℝ) ^ (-(1 : ℝ))) ^ k) Filter.atTop (nhds 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (three_rpow_nonneg _) ?_
    have h : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by rw [Real.rpow_neg_one]; norm_num
    rw [h]; norm_num
  have hform : ∀ k : ℕ,
      boxRadius (n - (k : ℤ)) = ((3 : ℝ) ^ ((n : ℝ) * 1) / 2) * ((3 : ℝ) ^ (-(1 : ℝ))) ^ k := by
    intro k
    rw [boxRadius_def, show ((((n - (k : ℤ)) : ℤ)) : ℝ) = ((n : ℝ) - (k : ℝ)) * 1 by
      push_cast; ring, three_rpow_sub_natCast_mul]
    ring
  simpa only [hform, mul_zero] using hpow.const_mul ((3 : ℝ) ^ ((n : ℝ) * 1) / 2)

/-- **(hLim), the convergence obligation.**  The regularizations converge to
the mollification `w ⋆ ψ` at *every* point, by continuity of the smooth
function `w ⋆ ψ` — no Lebesgue differentiation is used. -/
theorem tendsto_boxRegularization_atTop {w ψ : Vec d → ℝ}
    (hwI : Integrable w volume) (hψ : IsMollifierDensity ψ)
    (n : ℤ) (x : Vec d) :
    Filter.Tendsto (fun k : ℕ => boxRegularization (n - (k : ℤ)) ψ w x) Filter.atTop
      (nhds ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x)) := by
  have hU : Continuous (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) :=
    (contDiff_convolution_mollifier hwI.locallyIntegrable hψ).continuous
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.1 hU.continuousAt (ε / 2) (by linarith only [hε])
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_boxRadius_atTop n) δ hδ0
  refine ⟨N, fun k hk => ?_⟩
  have hrad : boxRadius (n - (k : ℤ)) < δ := by
    have h := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_pos (boxRadius_pos _)] at h
    exact h
  have hint : IntegrableOn (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)
      (boxSet (n - (k : ℤ)) x) volume :=
    ContinuousOn.integrableOn_compact (isCompact_boxSet _ x) hU.continuousOn
  have hbnd : |boxAverage (n - (k : ℤ)) x (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)
      - (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x| ≤ ε / 2 := by
    rw [← boxAverage_sub_const _ hint]
    refine abs_boxAverage_le ?_
    intro y hy
    have hdy : dist y x < δ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (mem_boxSet_iff.1 hy) hrad
    have := hδ hdy
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq, boxRegularization_def]
  exact lt_of_le_of_lt hbnd (by linarith only [hε])

end

end Algsuperdiff.Section4.Provider.Homogenization
