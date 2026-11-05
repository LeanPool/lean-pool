/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2

/-!
# FractionalPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The mean-zero fractional Poincaré inequality, at the Section-4 carriers

This module is a carrier-level utility for the Section 4 estimates.

## The estimate

For a set `W` of positive finite volume, `sup`-diameter at most `D`, and any
`f` integrable on `W`,

```text
  ‖f - ⨍_W f‖_{L²(W)}  ≤  D^{s + d/2} · |W|^{-1/2} · [f]_{H^s(W)} ,
```

with `[·]_{H^s(W)}` the manuscript's volume-normalized Gagliardo seminorm
`Support.normalizedGagliardoESeminormOn` and `‖·‖_{L²(W)}` its `ℝ≥0∞` reading
`eLpNorm · 2 (Support.normalizedVolumeMeasureOn W)` — the exact left-hand-side
carrier of the frozen Section-4 harmonic surface.

The constant is **`s`-uniform**: no factor degenerates as `s ↑ 1` or `s ↓ 0`,
and on the development's windows it collapses to a dimensional numeral (see
`FractionalPoincareWindow`).  No Sobolev embedding, no compactness and no inner
product enter: the ambient `Vec d = Fin d → ℝ` carries the supremum norm and
the proof uses only Jensen and the volume ratio.

## The three moves

1. **Jensen** (`eLpNorm_sub_integral_le_eLpNorm_prod`).  Against the probability
   measure `μ = ⨍_W`, `f x - ⨍_W f = ∫_y (f x - f y) dμ(y)`, so
   `‖f x - ⨍_W f‖ₑ ≤ ‖f x - f ·‖_{L¹(μ)} ≤ ‖f x - f ·‖_{L²(μ)}`
   (`eLpNorm_le_eLpNorm_of_exponent_le`, valid because `μ` is a probability
   measure).  Squaring and integrating in `x`, then Tonelli, gives
   `‖f - ⨍_W f‖_{L²(μ)} ≤ ‖f ·₁ - f ·₂‖_{L²(μ⊗μ)}`.
2. **The kernel** (`norm_sub_le_rpow_mul_norm_gagliardoKernel`).  Pointwise on
   `W × W`, `‖f x - f y‖ = |x-y|^{s+d/2}·‖K(x,y)‖ ≤ D^{s+d/2}·‖K(x,y)‖` with
   `K` CoarseGraining's `Gagliardo.gagliardoKernel s 2 f`; the diagonal is the
   trivial case `0 ≤ 0`.
3. **The normalization** (`normalizedGagliardoMeasureOn_eq_smul_prod`).  The
   manuscript's Gagliardo measure is normalized in `x` and *plain* volume in `y`,
   i.e. `ν = |W| · (μ ⊗ μ)`; the single factor `|W|^{-1/2}` is exactly that
   asymmetry, and it is what cancels the `D^d` half of `D^{s+d/2}`.

## References

* ABK26, `e.excess.def` (the `L²` carrier); the normalized fractional
  seminorm.
* `Algsuperdiff/Section4/Support/Dirichlet.lean` (`normalizedVolumeMeasureOn`,
  `normalizedGagliardoESeminormOn`).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

/-! ## 1. The `p = 2` `eLpNorm` as a `lintegral` -/

private theorem eLpNorm_two_eq_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

/-! ## 2. Jensen against a probability measure -/

section Jensen

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- **The pointwise Jensen step.**  Against a probability measure the deviation
of `f x` from the mean is controlled in `L²` by the two-point differences. -/
theorem enorm_sub_integral_rpow_two_le (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → E} (hf : Integrable f μ) (x : α) :
    ‖f x - ∫ y, f y ∂μ‖ₑ ^ (2 : ℝ) ≤ ∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ := by
  have hgm : AEStronglyMeasurable (fun y => f x - f y) μ :=
    aestronglyMeasurable_const.sub hf.aestronglyMeasurable
  have hint : ∫ y, (f x - f y) ∂μ = f x - ∫ y, f y ∂μ := by
    rw [integral_sub (integrable_const _) hf, integral_const]
    simp
  have h1 : ‖f x - ∫ y, f y ∂μ‖ₑ ≤ ∫⁻ y, ‖f x - f y‖ₑ ∂μ := by
    rw [← hint]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ y, ‖f x - f y‖ₑ ∂μ)
      ≤ (∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (p := 1) (q := 2)
      (f := fun y => f x - f y) (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm hgm, eLpNorm_two_eq_rpow _ hgm] at hcmp
  have h4 : ‖f x - ∫ y, f y ∂μ‖ₑ ^ (2 : ℝ)
      ≤ ((∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
  refine h4.trans (le_of_eq ?_)
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **Jensen at the `L²` level.**  The mean-subtracted `L²(μ)` norm is at most
the `L²(μ ⊗ μ)` norm of the two-point difference field. -/
theorem eLpNorm_sub_integral_le_eLpNorm_prod (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → E} (hf : Integrable f μ) :
    eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ
      ≤ eLpNorm (fun z : α × α => f z.1 - f z.2) 2 (μ.prod μ) := by
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [eLpNorm_two_eq_rpow (fun x => f x - ∫ y, f y ∂μ) (hfm.sub aestronglyMeasurable_const),
    eLpNorm_two_eq_rpow (fun z : α × α => f z.1 - f z.2) (hfm.comp_fst.sub hfm.comp_snd)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hmeas : AEMeasurable (fun z : α × α => ‖f z.1 - f z.2‖ₑ ^ (2 : ℝ)) (μ.prod μ) :=
    ((hfm.comp_fst.sub hfm.comp_snd).enorm).pow_const _
  rw [lintegral_prod _ hmeas]
  exact lintegral_mono fun x => enorm_sub_integral_rpow_two_le μ hf x

end Jensen

/-! ## 3. The pointwise kernel bound -/

variable {d : ℕ}

/-- **The kernel bound.**  On a set of `sup`-diameter at most `D` the raw increment
is `D^{s+d/2}` times CoarseGraining's difference-quotient kernel. -/
theorem norm_sub_le_rpow_mul_norm_gagliardoKernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s D : ℝ} (hs : 0 ≤ s) (f : Vec d → E) {x y : Vec d}
    (hxy : dist x y ≤ D) :
    ‖f x - f y‖ ≤ D ^ (s + (d : ℝ) / 2) * ‖Gagliardo.gagliardoKernel s 2 f (x, y)‖ := by
  have hexp : Gagliardo.kernelExponent d s 2 = s + (d : ℝ) / 2 := by
    rw [Gagliardo.kernelExponent]
    norm_num
  have he0 : (0 : ℝ) ≤ s + (d : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith only [hs, this]
  have hker : Gagliardo.gagliardoKernel s 2 f (x, y)
      = (dist x y ^ (-(s + (d : ℝ) / 2))) • (f x - f y) := by
    rw [Gagliardo.gagliardoKernel_apply, hexp]
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x y) with hd0 | hdpos
  · have hxy0 : x = y := dist_eq_zero.mp hd0.symm
    rw [hxy0, sub_self, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (le_trans dist_nonneg hxy) _) (norm_nonneg _)
  · have hnorm : ‖Gagliardo.gagliardoKernel s 2 f (x, y)‖
        = dist x y ^ (-(s + (d : ℝ) / 2)) * ‖f x - f y‖ := by
      rw [hker, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
    have hmono : dist x y ^ (s + (d : ℝ) / 2) ≤ D ^ (s + (d : ℝ) / 2) :=
      Real.rpow_le_rpow dist_nonneg hxy he0
    have hcancel : dist x y ^ (s + (d : ℝ) / 2) * dist x y ^ (-(s + (d : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hdpos, add_neg_cancel, Real.rpow_zero]
    rw [hnorm, ← mul_assoc]
    calc ‖f x - f y‖
        = dist x y ^ (s + (d : ℝ) / 2) * dist x y ^ (-(s + (d : ℝ) / 2)) * ‖f x - f y‖ := by
          rw [hcancel, one_mul]
      _ ≤ D ^ (s + (d : ℝ) / 2) * dist x y ^ (-(s + (d : ℝ) / 2)) * ‖f x - f y‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg dist_nonneg _)

/-! ## 4. The window measures -/

/-- The volume-normalized measure of a window of positive finite volume is a
probability measure. -/
theorem isProbabilityMeasure_normalizedVolumeMeasureOn {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) :
    IsProbabilityMeasure (normalizedVolumeMeasureOn W) := by
  refine ⟨?_⟩
  rw [normalizedVolumeMeasureOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hWpos.ne' hWtop

/-- The restricted volume is `|W|` times the normalized volume. -/
theorem restrict_eq_smul_normalizedVolumeMeasureOn {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) :
    volume.restrict W = (volume W) • normalizedVolumeMeasureOn W := by
  rw [normalizedVolumeMeasureOn_def, smul_smul, ENNReal.mul_inv_cancel hWpos.ne' hWtop,
    one_smul]

/-- **The asymmetry of the manuscript's Gagliardo normalization.**  It is `|W|`
times the symmetric probability square. -/
theorem normalizedGagliardoMeasureOn_eq_smul_prod {W : Set (Vec d)}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) :
    normalizedGagliardoMeasureOn W
      = (volume W) • ((normalizedVolumeMeasureOn W).prod (normalizedVolumeMeasureOn W)) := by
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hWpos hWtop
  rw [normalizedGagliardoMeasureOn_def, restrict_eq_smul_normalizedVolumeMeasureOn hWpos hWtop,
    Measure.prod_smul_right]

/-! ## 5. The estimate -/

/-- **The mean-zero fractional Poincaré inequality.**

For `W` of positive finite volume and `sup`-diameter at most `D`, and `f`
integrable on `W`,

```text
  ‖f - ⨍_W f‖_{L²(W)}  ≤  ( D^{s+d/2} / |W|^{1/2} ) · [f]_{H^s(W)} .
```

The constant is `s`-uniform: it is a single `rpow` of the diameter against the
volume, with no `(1-s)^{-1}` or `s^{-1}` anywhere.  Both sides are the frozen
Section-4 surface's own carriers. -/
theorem eLpNorm_sub_integral_le_normalizedGagliardoESeminormOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {W : Set (Vec d)} {s D : ℝ} {f : Vec d → E}
    (hW : MeasurableSet W) (hWpos : 0 < volume W) (hWtop : volume W ≠ ⊤) (hs : 0 ≤ s)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, dist x y ≤ D)
    (hf : Integrable f (volume.restrict W)) :
    eLpNorm (fun x => f x - ∫ y, f y ∂(normalizedVolumeMeasureOn W)) 2
        (normalizedVolumeMeasureOn W)
      ≤ ENNReal.ofReal (D ^ (s + (d : ℝ) / 2) / Real.sqrt ((volume W).toReal))
          * normalizedGagliardoESeminormOn W s f := by
  classical
  have hprob := isProbabilityMeasure_normalizedVolumeMeasureOn hWpos hWtop
  set μ : Measure (Vec d) := normalizedVolumeMeasureOn W with hμ
  set e : ℝ := s + (d : ℝ) / 2 with he
  -- the data
  have hD0 : 0 ≤ D := by
    obtain ⟨x, hx⟩ : W.Nonempty := nonempty_of_measure_ne_zero hWpos.ne'
    simpa using hdiam x hx x hx
  have hfμ : Integrable f μ := by
    rw [hμ, normalizedVolumeMeasureOn_def]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hWpos.ne')
  have haeW : ∀ᵐ x ∂μ, x ∈ W := by
    rw [hμ, normalizedVolumeMeasureOn_def]
    exact Measure.ae_smul_measure (ae_restrict_mem hW) _
  have hae1 : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ W := Measure.quasiMeasurePreserving_fst.ae haeW
  have hae2 : ∀ᵐ z ∂(μ.prod μ), z.2 ∈ W := Measure.quasiMeasurePreserving_snd.ae haeW
  have hdiffm : AEStronglyMeasurable (fun z : Vec d × Vec d => f z.1 - f z.2) (μ.prod μ) :=
    hfμ.aestronglyMeasurable.comp_fst.sub hfμ.aestronglyMeasurable.comp_snd
  have hkerm : AEStronglyMeasurable (Gagliardo.gagliardoKernel s 2 f) (μ.prod μ) := by
    have hscal : AEStronglyMeasurable
        (fun z : Vec d × Vec d => dist z.1 z.2 ^ (-(Gagliardo.kernelExponent d s 2)))
        (μ.prod μ) :=
      (measurable_dist.pow measurable_const).aestronglyMeasurable
    exact hscal.smul hdiffm
  -- move 2: the pointwise kernel domination
  have hstep2 : eLpNorm (fun z : Vec d × Vec d => f z.1 - f z.2) 2 (μ.prod μ)
      ≤ ENNReal.ofReal (D ^ e) * eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (μ.prod μ) := by
    have hmono : eLpNorm (fun z : Vec d × Vec d => f z.1 - f z.2) 2 (μ.prod μ)
        ≤ eLpNorm ((D ^ e) • (Gagliardo.gagliardoKernel s 2 f)) 2 (μ.prod μ) := by
      refine eLpNorm_mono_ae hdiffm ?_
      filter_upwards [hae1, hae2] with z hz1 hz2
      have hb := norm_sub_le_rpow_mul_norm_gagliardoKernel (d := d) (D := D) hs f
        (hdiam z.1 hz1 z.2 hz2)
      refine hb.trans (le_of_eq ?_)
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hD0 _)]
    refine hmono.trans (le_of_eq ?_)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg hD0 _)]
  -- move 3: the normalization
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]
    norm_num
  have hVpow0 : (volume W) ^ ((1 : ℝ) / 2) ≠ 0 := (ENNReal.rpow_pos hWpos hWtop).ne'
  have hVpowtop : (volume W) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hWtop).ne
  have hker : normalizedGagliardoESeminormOn W s f
      = (volume W) ^ ((1 : ℝ) / 2)
          * eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (μ.prod μ) := by
    rw [normalizedGagliardoESeminormOn_def,
      normalizedGagliardoMeasureOn_eq_smul_prod hWpos hWtop, ← hμ,
      eLpNorm_smul_measure_of_ne_top (by norm_num) _ (volume W) hkerm, smul_eq_mul, hhalf]
  have hkerinv : eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (μ.prod μ)
      = ((volume W) ^ ((1 : ℝ) / 2))⁻¹ * normalizedGagliardoESeminormOn W s f := by
    rw [hker, ← mul_assoc, ENNReal.inv_mul_cancel hVpow0 hVpowtop, one_mul]
  -- the constant
  have hVreal : (0 : ℝ) < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hsqrt : (volume W) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt ((volume W).toReal)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos hVreal, ENNReal.ofReal_toReal hWtop]
  have hconst : ENNReal.ofReal (D ^ e) * ((volume W) ^ ((1 : ℝ) / 2))⁻¹
      = ENNReal.ofReal (D ^ e / Real.sqrt ((volume W).toReal)) := by
    rw [hsqrt, ← ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hVreal),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD0 _), div_eq_mul_inv]
  -- assembly
  calc eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ
      ≤ eLpNorm (fun z : Vec d × Vec d => f z.1 - f z.2) 2 (μ.prod μ) :=
        eLpNorm_sub_integral_le_eLpNorm_prod μ hfμ
    _ ≤ ENNReal.ofReal (D ^ e) * eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (μ.prod μ) :=
        hstep2
    _ = ENNReal.ofReal (D ^ e) * ((volume W) ^ ((1 : ℝ) / 2))⁻¹
          * normalizedGagliardoESeminormOn W s f := by
        rw [hkerinv, mul_assoc]
    _ = ENNReal.ofReal (D ^ e / Real.sqrt ((volume W).toReal))
          * normalizedGagliardoESeminormOn W s f := by rw [hconst]

/-! ## 6. The development's average carriers -/

/-- The abstract average against `normalizedVolumeMeasureOn W` **is**
CoarseGraining's `volumeAverageVec` on vector fields integrable on `W`. -/
theorem integral_normalizedVolumeMeasureOn_eq_volumeAverageVec {W : Set (Vec d)}
    {f : Vec d → Vec d} (hf : Integrable f (volume.restrict W)) :
    ∫ y, f y ∂(normalizedVolumeMeasureOn W) = volumeAverageVec W f := by
  funext i
  have hproj : ∫ y in W, f y i = (∫ y in W, f y) i := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integral_comp_comm hf
    exact this
  rw [normalizedVolumeMeasureOn_def, integral_smul_measure, volumeAverageVec, volumeAverage,
    ENNReal.toReal_inv, Pi.smul_apply, smul_eq_mul, hproj]

end

end Algsuperdiff.Section4.Provider.Regularity
