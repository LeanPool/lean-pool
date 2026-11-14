/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.HolderGagliardoRadial
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# HolderGagliardoEmbedding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `C^{0,1/2}(A) ↪ H^s(A)` for `s < 1/2`, on an arbitrary window

Nothing here imports that file, nothing here claims the anchor, and nothing
here is a frozen statement.

## The target

This module proves the window-free content of it — the Hölder-into- Gagliardo
embedding at a general fractional index with the honest constant — and
`StepFourSeminormComparisons` instantiates it at the Step-3 windows.

```text
  |g(x) - g(y)| ≤ K |x-y|^{1/2}  on A ,   A ⊆ B(x,R) for every x ∈ A ,
  0 < s < 1/2 ,  1 ≤ d
      ⟹  [g]_{H^s(A)} ≤ K · ( C_rad(d, d+2s-1) · R^{d} · R^{-(d+2s-1)} )^{1/2} .
```

Since `R^{d}·R^{-(d+2s-1)} = R^{1-2s}`, the right side is `K·C(d,s)·R^{1/2-s}`;
at `s = 1/4` this is the manuscript's `3^{j/4}` once `R := 3^j`.

## The volume normalization is inert

The manuscript's `[·]_{H^s(A)}` averages in the *first* slot only.  Bounding
the inner integral uniformly over the first slot and integrating against a
probability measure returns the bound with no volume factor at all: the estimate
below is normalization-free, which is why the printed `C` carries no `|U_j|`.

## References

* ABK26, `t.regularity` Step 4.
* ABK26, (`[·]_{W^{s,p}}`), (`[·]_{C^{0,α}}` and the `p = ∞` identification).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory Metric
open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The Gagliardo exponent of a `C^{0,1/2}` field -/

/-- `β(d,s) = d + 2s - 1`: the singularity exponent of the Gagliardo integrand
of a `C^{0,1/2}` field at fractional index `s`. -/
def holderGagliardoBeta (d : ℕ) (s : ℝ) : ℝ := (d : ℝ) + 2 * s - 1

theorem holderGagliardoBeta_pos {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) :
    0 < holderGagliardoBeta d s := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [holderGagliardoBeta]
  linarith only [hd', hs0]

theorem holderGagliardoBeta_lt {s : ℝ} (hs : s < 1 / 2) :
    holderGagliardoBeta d s < (d : ℝ) := by
  rw [holderGagliardoBeta]
  linarith only [hs]

/-! ## 2. The pointwise majorant on the Gagliardo kernel -/

private theorem enorm_gagliardoKernel_sq_le {A : Set (Vec d)} {g : Vec d → E} {K s : ℝ}
    (hK : 0 ≤ K) (hg : Support.HolderSeminormBoundOn A (1 / 2) K g)
    {z : Vec d × Vec d} (h1 : z.1 ∈ A) (h2 : z.2 ∈ A) :
    ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (K ^ 2) * ‖z.1 - z.2‖ₑ ^ (-holderGagliardoBeta d s) := by
  have hker : Gagliardo.gagliardoKernel s 2 g z =
      (dist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) • (g z.1 - g z.2) := by
    rw [Gagliardo.gagliardoKernel_apply, Gagliardo.kernelExponent]
    norm_num
  rcases eq_or_ne z.1 z.2 with heq | hne
  · have hzero : Gagliardo.gagliardoKernel s 2 g z = 0 := by
      rw [hker, heq, sub_self, smul_zero]
    rw [hzero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  have ht : 0 < dist z.1 z.2 := dist_pos.mpr hne
  have henorm : ‖z.1 - z.2‖ₑ = ENNReal.ofReal (dist z.1 z.2) := by
    rw [dist_eq_norm, ← ofReal_norm]
  set t : ℝ := dist z.1 z.2 with htdef
  set M : ℝ := t ^ (-(s + (d : ℝ) / 2)) * (K * t ^ ((1 : ℝ) / 2)) with hMdef
  have hM0 : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ t ^ (-(s + (d : ℝ) / 2)) := Real.rpow_nonneg ht.le _
    have h2 : (0 : ℝ) ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ht.le _
    rw [hMdef]
    positivity
  have hbound : ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ≤ ENNReal.ofReal M := by
    have hscal : ‖(dist z.1 z.2 ^ (-(s + (d : ℝ) / 2)) : ℝ)‖ₑ =
        ENNReal.ofReal (t ^ (-(s + (d : ℝ) / 2))) := by
      rw [← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hdiff : ‖g z.1 - g z.2‖ₑ ≤ ENNReal.ofReal (K * t ^ ((1 : ℝ) / 2)) := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hgb := hg z.1 h1 z.2 h2
      have hd12 : ‖z.1 - z.2‖ = t := (dist_eq_norm z.1 z.2).symm
      rw [hd12] at hgb
      exact hgb
    rw [hker, enorm_smul, hscal, hMdef, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    exact mul_le_mul' le_rfl hdiff
  have hreal : M ^ (2 : ℕ) = K ^ 2 * t ^ (-holderGagliardoBeta d s) := by
    have hprod : t ^ (-(s + (d : ℝ) / 2)) * t ^ ((1 : ℝ) / 2) =
        t ^ (-(s + (d : ℝ) / 2) + (1 : ℝ) / 2) := (Real.rpow_add ht _ _).symm
    have hsq : (t ^ (-(s + (d : ℝ) / 2) + (1 : ℝ) / 2)) ^ (2 : ℕ) =
        t ^ (-holderGagliardoBeta d s) := by
      rw [← Real.rpow_natCast (t ^ (-(s + (d : ℝ) / 2) + (1 : ℝ) / 2)) 2,
        ← Real.rpow_mul ht.le]
      congr 1
      rw [holderGagliardoBeta]
      push_cast
      ring
    calc M ^ (2 : ℕ)
        = K ^ 2 * (t ^ (-(s + (d : ℝ) / 2)) * t ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
          rw [hMdef]; ring
      _ = K ^ 2 * (t ^ (-(s + (d : ℝ) / 2) + (1 : ℝ) / 2)) ^ (2 : ℕ) := by rw [hprod]
      _ = K ^ 2 * t ^ (-holderGagliardoBeta d s) := by rw [hsq]
  have hsquare : (ENNReal.ofReal M) ^ (2 : ℝ) =
      ENNReal.ofReal (K ^ 2) * ‖z.1 - z.2‖ₑ ^ (-holderGagliardoBeta d s) := by
    have hrp : M ^ (2 : ℝ) = M ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast M 2]
      norm_num
    rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num : (0 : ℝ) ≤ 2), hrp, hreal,
      ENNReal.ofReal_mul (by positivity), henorm, ENNReal.ofReal_rpow_of_pos ht]
  rw [← hsquare]
  exact ENNReal.rpow_le_rpow hbound (by norm_num)

/-- A Hölder-`1/2` bound on `A` makes the Gagliardo kernel a.e. strongly measurable on
the normalized product measure of `A`. -/
private theorem aestronglyMeasurable_gagliardoKernel_of_holderHalfBound {A : Set (Vec d)}
    {g : Vec d → E} {K s : ℝ} (hA : MeasurableSet A) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn A (1 / 2) K g) :
    AEStronglyMeasurable (Gagliardo.gagliardoKernel s 2 g)
      (Support.normalizedGagliardoMeasureOn A) := by
  have hcont : ContinuousOn g A := by
    rw [Metric.continuousOn_iff]
    intro b hb eps heps
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    have hq : (0 : ℝ) < eps / (K + 1) := div_pos heps hK1
    refine ⟨(eps / (K + 1)) ^ (2 : ℝ), by positivity, fun a ha hab => ?_⟩
    have hnorm : ‖a - b‖ < (eps / (K + 1)) ^ (2 : ℝ) := by
      rwa [← dist_eq_norm]
    have hpow : ‖a - b‖ ^ ((1 : ℝ) / 2) ≤ eps / (K + 1) := by
      refine le_of_lt ?_
      calc ‖a - b‖ ^ ((1 : ℝ) / 2) < ((eps / (K + 1)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_lt_rpow (norm_nonneg _) hnorm (by norm_num)
        _ = eps / (K + 1) := by
            rw [← Real.rpow_mul hq.le]
            norm_num
    have hbd := hg a ha b hb
    have hstep : K * ‖a - b‖ ^ ((1 : ℝ) / 2) ≤ K * (eps / (K + 1)) :=
      mul_le_mul_of_nonneg_left hpow hK
    have hfrac : K * (eps / (K + 1)) < eps := by
      have hle : K / (K + 1) < 1 := (div_lt_one hK1).2 (by linarith)
      calc K * (eps / (K + 1)) = eps * (K / (K + 1)) := by ring
        _ < eps * 1 := mul_lt_mul_of_pos_left hle heps
        _ = eps := mul_one eps
    rw [dist_eq_norm]
    linarith [hbd, hstep, hfrac]
  have hmu : Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
    rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
      Measure.prod_smul_left, Measure.prod_restrict]
  rw [hmu]
  refine AEStronglyMeasurable.smul_measure ?_ _
  have hscal : AEStronglyMeasurable
      (fun z : Vec d × Vec d => dist z.1 z.2 ^ (-(Gagliardo.kernelExponent d s 2)))
      ((volume.prod volume).restrict (A ×ˢ A)) :=
    (measurable_dist.pow measurable_const).aestronglyMeasurable
  have hfst : ContinuousOn (fun z : Vec d × Vec d => g z.1) (A ×ˢ A) :=
    hcont.comp continuous_fst.continuousOn fun _ hz => hz.1
  have hsnd : ContinuousOn (fun z : Vec d × Vec d => g z.2) (A ×ˢ A) :=
    hcont.comp continuous_snd.continuousOn fun _ hz => hz.2
  have hvec : AEStronglyMeasurable (fun z : Vec d × Vec d => g z.1 - g z.2)
      ((volume.prod volume).restrict (A ×ˢ A)) :=
    (hfst.sub hsnd).aestronglyMeasurable (hA.prod hA)
  exact hscal.smul hvec

/-! ## 3. The embedding -/

/-- If `g` obeys the Hölder-`1/2` bound `K` on `A`, if `A` has `sup`-diameter at
most `R` (in the form `A ⊆ B(x,R)` for every `x ∈ A`), and if `0 < s < 1/2`,
then the volume-normalized Gagliardo seminorm of `g` on `A` is at most `K ·
(C_rad(d,β) · R^d · R^{-β})^{1/2}` with `β = d + 2s - 1`, i.e. `K · C(d,s) ·
R^{1/2-s}`. -/
theorem normalizedGagliardoESeminormOn_le_of_holderHalf {A : Set (Vec d)} {g : Vec d → E}
    {K R s : ℝ} (hd : 1 ≤ d) (hAmeas : MeasurableSet A) (hA0 : volume A ≠ 0)
    (hAtop : volume A ≠ ⊤) (hball : ∀ x ∈ A, A ⊆ Metric.ball x R) (hR : 0 < R)
    (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn A (1 / 2) K g) :
    Support.normalizedGagliardoESeminormOn A s g ≤
      ENNReal.ofReal (K * Real.sqrt (radialKernelConst d (holderGagliardoBeta d s) *
        (R ^ d * R ^ (-holderGagliardoBeta d s)))) := by
  have hbpos : 0 < holderGagliardoBeta d s := holderGagliardoBeta_pos hd hs0
  have hblt : holderGagliardoBeta d s < (d : ℝ) := holderGagliardoBeta_lt hs
  have hcnn : (0 : ℝ) ≤ radialKernelConst d (holderGagliardoBeta d s) *
      (R ^ d * R ^ (-holderGagliardoBeta d s)) := by
    have h1 := (radialKernelConst_pos hblt).le
    have h2 : (0 : ℝ) < R ^ d := by positivity
    have h3 : (0 : ℝ) < R ^ (-holderGagliardoBeta d s) := Real.rpow_pos_of_pos hR _
    positivity
  set M : ℝ≥0∞ := ENNReal.ofReal (radialKernelConst d (holderGagliardoBeta d s) *
    (R ^ d * R ^ (-holderGagliardoBeta d s))) with hMdef
  have hkermeas : Measurable fun z : Vec d × Vec d =>
      ‖z.1 - z.2‖ₑ ^ (-holderGagliardoBeta d s) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_fst.sub measurable_snd).enorm
  have hmu : Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
    rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
      Measure.prod_smul_left, Measure.prod_restrict]
  have hinner : ∫⁻ z in A ×ˢ A, ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ^ (2 : ℝ)
        ∂(volume.prod volume) ≤ ENNReal.ofReal (K ^ 2) * (M * volume A) := by
    calc ∫⁻ z in A ×ˢ A, ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)
        ≤ ∫⁻ z in A ×ˢ A, ENNReal.ofReal (K ^ 2) *
            ‖z.1 - z.2‖ₑ ^ (-holderGagliardoBeta d s) ∂(volume.prod volume) :=
          setLIntegral_mono' (hAmeas.prod hAmeas)
            fun z hz => enorm_gagliardoKernel_sq_le hK hg hz.1 hz.2
      _ = ENNReal.ofReal (K ^ 2) *
            ∫⁻ z in A ×ˢ A, ‖z.1 - z.2‖ₑ ^ (-holderGagliardoBeta d s) ∂(volume.prod volume) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (K ^ 2) *
            ∫⁻ x in A, ∫⁻ y in A, ‖x - y‖ₑ ^ (-holderGagliardoBeta d s) ∂volume ∂volume := by
          rw [← Measure.prod_restrict]
          rw [MeasureTheory.lintegral_prod _ hkermeas.aemeasurable]
      _ ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ _ in A, M ∂volume :=
          mul_le_mul' le_rfl (setLIntegral_mono' hAmeas fun x hx =>
            lintegral_enorm_sub_rpow_neg_le_of_subset_ball (hball x hx) hR hbpos hblt)
      _ = ENNReal.ofReal (K ^ 2) * (M * volume A) := by rw [setLIntegral_const]
  have hkey : ∫⁻ z, ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ^ (2 : ℝ)
        ∂(Support.normalizedGagliardoMeasureOn A) ≤ ENNReal.ofReal (K ^ 2) * M := by
    rw [hmu, lintegral_smul_measure]
    calc (volume A)⁻¹ * ∫⁻ z in A ×ˢ A, ‖Gagliardo.gagliardoKernel s 2 g z‖ₑ ^ (2 : ℝ)
          ∂(volume.prod volume)
        ≤ (volume A)⁻¹ * (ENNReal.ofReal (K ^ 2) * (M * volume A)) :=
          mul_le_mul' le_rfl hinner
      _ = ENNReal.ofReal (K ^ 2) * M * ((volume A)⁻¹ * volume A) := by ring
      _ = ENNReal.ofReal (K ^ 2) * M := by
          rw [ENNReal.inv_mul_cancel hA0 hAtop, mul_one]
  rw [Support.normalizedGagliardoESeminormOn_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aestronglyMeasurable_gagliardoKernel_of_holderHalfBound hAmeas hK hg)]
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htwo]
  refine (ENNReal.rpow_le_rpow hkey (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hMdef,
    ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ K ^ 2) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hcnn (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hK]

end

end Algsuperdiff.Section4.Provider.Regularity
