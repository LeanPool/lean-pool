/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingState
public import LeanPool.LiebThirring.Fourier.Functoriality

/-! # Interchanging L² slices and partial Fourier transformation

Product currying supplies genuine L² classes in both orders. The interchange
of a partial Fourier transform is proved on scalar tensors and extended by
L² density; it does not assert pointwise Fourier integration for an L² state.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.Assembly

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ν : Measure α} [SFinite ν]
  [SecondCountableTopology (Lp E 2 ν)]
  [SecondCountableTopology (Lp E 2 (volume : Measure Position))]

/-- Interchange the outer spatial variable and the remaining L² variable. -/
@[expose] noncomputable def realFormSwapCurrying :
    Lp (Lp E 2 ν) 2 (volume : Measure Position) ≃ₗᵢ[ℂ]
      Lp (Lp E 2 (volume : Measure Position)) 2 ν :=
  (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position)) (ν := ν)
    (E := E)).symm |>.trans
    (l2PullbackEquiv (E := E) (MeasurableEquiv.prodComm (α := α) (β := Position))
      Measure.measurePreserving_swap) |>.trans
    (l2CurryLinearIsometryEquiv (μ := ν) (ν := (volume : Measure Position)) (E := E))

/-- Exchanging slices is currying the swapped product class. -/
theorem realFormSwapCurrying_apply (u : Lp (Lp E 2 ν) 2 (volume : Measure Position)) :
    realFormSwapCurrying u = l2Curry
      (l2PullbackEquiv (E := E)
        (MeasurableEquiv.prodComm (α := α) (β := Position)) Measure.measurePreserving_swap
        ((l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
          (ν := ν) (E := E)).symm u)) := rfl

/-- The exchanged class agrees with the uncurried product representative,
in the order needed to apply the one-body estimate on each remaining slice. -/
theorem realFormSwapCurrying_ae_uncurry
    (u : Lp (Lp E 2 ν) 2 (volume : Measure Position)) :
    ∀ᵐ y ∂ν, ∀ᵐ x : Position, realFormSwapCurrying u y x =
      ((l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
        (ν := ν) (E := E)).symm u) (x, y) := by
  let f := (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := ν) (E := E)).symm u
  let g := l2PullbackEquiv (E := E)
    (MeasurableEquiv.prodComm (α := α) (β := Position)) Measure.measurePreserving_swap f
  change ∀ᵐ y ∂ν, ∀ᵐ x : Position, l2Curry g y x = f (x, y)
  filter_upwards [l2Curry_ae g, Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (MeasurableEquiv.prodComm (α := α) (β := Position)) Measure.measurePreserving_swap f)]
    with y hy ht
  filter_upwards [hy, ht] with x hx htx
  exact hx.trans htx

/-- Weighted spatial mass is unchanged by exchanging the slice order. -/
theorem realFormSwapCurrying_weighted_norm_sq
    (u : Lp (Lp E 2 ν) 2 (volume : Measure Position))
    (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y, ∫⁻ x : Position, w x * ‖realFormSwapCurrying u y x‖ₑ ^ 2 ∂(volume : Measure Position)
      ∂ν) =
      ∫⁻ x : Position, w x * ‖u x‖ₑ ^ 2 := by
  let f := (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
    (ν := ν) (E := E)).symm u
  have hc : ∀ᵐ x : Position, ∀ᵐ y ∂ν, u x y = f (x, y) := by
    have h := l2Curry_ae f
    rw [show l2Curry f = u from
      (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
        (ν := ν) (E := E)).apply_symm_apply u] at h
    exact h
  calc
    _ = ∫⁻ y, ∫⁻ x : Position, w x * ‖f (x, y)‖ₑ ^ 2 ∂(volume : Measure Position) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [realFormSwapCurrying_ae_uncurry u] with y hy
      exact lintegral_congr_ae (hy.mono fun x hx => congrArg (fun a : E => w x * ‖a‖ₑ ^ 2) hx)
    _ = ∫⁻ x : Position, ∫⁻ y, w x * ‖f (x, y)‖ₑ ^ 2 ∂ν := by
      exact (lintegral_lintegral_swap
        ((hw.comp measurable_fst).mul ((Lp.stronglyMeasurable f).enorm.pow_const
          2)).aemeasurable).symm
    _ = ∫⁻ x : Position, w x * ‖u x‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [hc] with x hx
      rw [lintegral_const_mul (w x)
        (f := fun y => ‖f (x, y)‖ₑ ^ 2)
        (((Lp.stronglyMeasurable f).comp_measurable
          (measurable_prodMk_left (x := x))).enorm.pow_const 2),
        ← lintegral_l2_enorm_sq (u x)]
      congr 1
      exact lintegral_congr_ae (hx.mono fun y hy => congrArg (fun a : E => ‖a‖ₑ ^ 2) hy.symm)

/-- Scalar tensor insertion into a Hilbert-valued spatial L² space. -/
@[expose] noncomputable def realFormScalarInsertion
    (f : Lp ℂ 2 (volume : Measure Position)) : E →L[ℂ] Lp E 2 (volume : Measure Position) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).flip.compLpL₂ 2 volume).flip f

omit [CompleteSpace E] [SecondCountableTopology (Lp E 2 (volume : Measure Position))] in
theorem realFormScalarInsertion_ae (f : Lp ℂ 2 (volume : Measure Position)) (v : E) :
    realFormScalarInsertion f v =ᵐ[volume] fun x => f x • v :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f

omit [CompleteSpace E] [SecondCountableTopology (Lp E 2 ν)]
  [SecondCountableTopology (Lp E 2 (volume : Measure Position))] in
private theorem memLp_realFormTensor (f : Lp ℂ 2 (volume : Measure Position))
    (v : Lp E 2 ν) :
    MemLp (fun z : Position × α => f z.1 • v z.2) 2 ((volume : Measure Position).prod ν) := by
  have hm : StronglyMeasurable (fun z : Position × α => f z.1 • v z.2) :=
    ((Lp.stronglyMeasurable f).comp_measurable measurable_fst).smul
      ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hm.aestronglyMeasurable).mpr
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_smul, mul_pow]
  rw [lintegral_prod_mul ((Lp.stronglyMeasurable f).enorm.pow_const 2).aemeasurable
    ((Lp.stronglyMeasurable v).enorm.pow_const 2).aemeasurable,
    lintegral_l2_enorm_sq, lintegral_l2_enorm_sq]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
    (ENNReal.pow_lt_top ENNReal.coe_lt_top)

/-- Slice interchange on an elementary scalar tensor. -/
theorem realFormSwapCurrying_tensor (f : Lp ℂ 2 (volume : Measure Position))
    (v : Lp E 2 ν) :
    realFormSwapCurrying ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) =
      (realFormScalarInsertion f).compLp v := by
  let h := memLp_realFormTensor f v
  let w := h.toLp (fun z : Position × α => f z.1 • v z.2)
  have hw : ∀ᵐ x : Position, ∀ᵐ y ∂ν, w (x, y) = f x • v y :=
    Measure.ae_ae_of_ae_prod h.coeFn_toLp
  have hc : l2Curry w = (ContinuousLinearMap.toSpanSingleton ℂ v).compLp f := by
    apply Lp.ext
    filter_upwards [l2Curry_ae w,
      (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f, hw] with x hx ht hwx
    rw [ht]
    apply Lp.ext
    filter_upwards [hx, hwx, Lp.coeFn_smul (f x) v] with y hxy hwy hsy
    exact hxy.trans (hwy.trans hsy.symm)
  have hinv : (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
      (ν := ν) (E := E)).symm ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) = w := by
    rw [← hc]
    exact (l2CurryLinearIsometryEquiv (μ := (volume : Measure Position))
      (ν := ν) (E := E)).symm_apply_apply w
  rw [realFormSwapCurrying_apply, hinv]
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := ν)
    (ν := (volume : Measure Position))).quasiMeasurePreserving.ae h.coeFn_toLp
  filter_upwards [l2Curry_ae
      (l2PullbackEquiv (E := E) (MeasurableEquiv.prodComm (α := α) (β := Position))
        Measure.measurePreserving_swap w),
    Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
      (MeasurableEquiv.prodComm (α := α) (β := Position)) Measure.measurePreserving_swap w),
    Measure.ae_ae_of_ae_prod hp,
    (realFormScalarInsertion f).coeFn_compLp v] with y hy ht hw' hr
  rw [hr]
  apply Lp.ext
  filter_upwards [hy, ht, hw', realFormScalarInsertion_ae f (v y)]
    with x hyx htx hwx hrx
  exact hyx.trans (htx.trans (hwx.trans hrx.symm))

private theorem continuousLinearMap_ext_scalarTensor
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A B : Lp H 2 (volume : Measure Position) →L[ℂ] K)
    (h : ∀ (f : Lp ℂ 2 (volume : Measure Position)) (v : H),
      A ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) =
        B ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.induction (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Position))
    (by norm_num) (fun u => A u = B u)
  · intro v s hs hμs
    let f : Lp ℂ 2 (volume : Measure Position) := indicatorConstLp 2 hs hμs.ne 1
    have heq : Lp.simpleFunc.indicatorConst 2 hs hμs.ne v =
        (ContinuousLinearMap.toSpanSingleton ℂ v).compLp f := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      apply Lp.ext
      filter_upwards [show ∀ᵐ x : Position,
          (indicatorConstLp 2 hs hμs.ne v : Lp H 2 volume) x = s.indicator (fun _ => v) x
          from indicatorConstLp_coeFn,
        (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f,
        show ∀ᵐ x : Position, f x = s.indicator (fun _ => (1 : ℂ)) x
          from indicatorConstLp_coeFn] with x hx ht hf
      rw [hx, ht, hf]
      by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_mem hxs, ContinuousLinearMap.toSpanSingleton_apply,
          one_smul]
      · simp only [Set.indicator_of_notMem hxs, ContinuousLinearMap.toSpanSingleton_apply,
          zero_smul]
    rw [heq]
    exact h f v
  · intro f g hf hg hd hAf hAg
    simpa only [map_add] using congrArg₂ (· + ·) hAf hAg
  · exact isClosed_eq A.continuous B.continuous

/-- Partial Fourier transformation commutes with exchanging the slice order. -/
theorem realFormSwapCurrying_fourier
    (u : Lp (Lp E 2 ν) 2 (volume : Measure Position)) :
    realFormSwapCurrying (𝓕 u) =
      (Lp.fourierTransformₗᵢ Position E).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (realFormSwapCurrying u) := by
  let S := (realFormSwapCurrying (E := E) (ν := ν)).toContinuousLinearEquiv.toContinuousLinearMap
  let F := (Lp.fourierTransformₗᵢ Position E).toContinuousLinearEquiv.toContinuousLinearMap
  let Fout := (Lp.fourierTransformₗᵢ Position (Lp E 2
    ν)).toContinuousLinearEquiv.toContinuousLinearMap
  have heq : S.comp Fout = (F.compLpL 2 ν).comp S := by
    apply continuousLinearMap_ext_scalarTensor
    intro f v
    change realFormSwapCurrying (𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f)) =
      F.compLp (realFormSwapCurrying ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f))
    rw [Fourier.fourier_compLp, realFormSwapCurrying_tensor, realFormSwapCurrying_tensor]
    apply Lp.ext
    filter_upwards [(realFormScalarInsertion (𝓕 f)).coeFn_compLp v,
      F.coeFn_compLp ((realFormScalarInsertion f).compLp v),
      (realFormScalarInsertion f).coeFn_compLp v] with y hl hr hv
    rw [hl, hr, hv]
    change (ContinuousLinearMap.toSpanSingleton ℂ (v y)).compLp (𝓕 f) =
      𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ (v y)).compLp f)
    exact (Fourier.fourier_compLp _ f).symm
  exact congrArg (fun T => T u) heq

/-- The integral of the slice Fourier energies is the outer partial Fourier energy. -/
theorem realFormSwapCurrying_fourier_weighted_norm_sq
    (u : Lp (Lp E 2 ν) 2 (volume : Measure Position))
    (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y, ∫⁻ ξ : Position, w ξ *
      ‖(𝓕 (realFormSwapCurrying u y) : Lp E 2 volume) ξ‖ₑ ^ 2
      ∂(volume : Measure Position) ∂ν) =
      ∫⁻ ξ : Position, w ξ * ‖(𝓕 u : Lp (Lp E 2 ν) 2 volume) ξ‖ₑ ^ 2 := by
  rw [← realFormSwapCurrying_weighted_norm_sq (𝓕 u) w hw,
    realFormSwapCurrying_fourier]
  apply lintegral_congr_ae
  filter_upwards [(Lp.fourierTransformₗᵢ Position
    E).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (realFormSwapCurrying u)] with y hy
  rw [hy]
  rfl

/-- Target isometries preserve all weighted extended L² masses. -/
theorem realFormTargetIsometry_weighted_norm_sq
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H ≃ₗᵢ[ℂ] K) (u : Lp H 2 (volume : Measure Position))
    (w : Position → ℝ≥0∞) :
    (∫⁻ x : Position, w x *
      (‖A.toContinuousLinearEquiv.toContinuousLinearMap.compLp u x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Position, w x * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
  apply lintegral_congr_ae
  filter_upwards [A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp u] with x hx
  rw [hx]
  exact congrArg (fun a : ℝ≥0 => w x * (a : ℝ≥0∞) ^ 2) (A.nnnorm_map (u x))

end LiebThirring.Assembly
end
