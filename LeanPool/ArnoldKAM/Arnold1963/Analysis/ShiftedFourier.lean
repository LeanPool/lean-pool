/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierDecay
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierSeries

/-!
Fourier reconstruction on shifted real tori inside the complex angle strip.
-/

@[expose] public section
noncomputable section
open Complex MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963

/-- Normalized Haar measure for contour-shifted Fourier integration. -/
local instance shiftedFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierMonomial_add {n : ℕ} (k : FourierIndex n) (q z : ComplexSpace n) :
    fourierMonomial k (q + z) = fourierMonomial k q * fourierMonomial k z := by
  simp [fourierMonomial, indexPairing, mul_add, Finset.sum_add_distrib, exp_add]

theorem fourierMonomial_neg_mul {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    fourierMonomial (-k) q * fourierMonomial k q = 1 := by
  simp only [fourierMonomial, indexPairing, Pi.neg_apply, Int.cast_neg, neg_mul,
    Finset.sum_neg_distrib, mul_neg, ← exp_add, neg_add_cancel, exp_zero]

theorem unitFourierWeight_eq_monomial {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    unitFourierWeight k q = fourierMonomial (-k) (angleScale n q) := by
  unfold unitFourierWeight fourierMonomial indexPairing
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.neg_apply, Int.cast_neg, angleScale_apply]
  ring

theorem angleScale_shift_split {n : ℕ} (y x : RealSpace n) :
    angleScale n (complexShift y x) = scaledAngle x + angleScale n (complexShift y 0) := by
  ext j
  simp [complexShift, scaledAngle, complexify, mul_add]

theorem unitFourierWeight_shift_split {n : ℕ} (k : FourierIndex n) (y x : RealSpace n) :
    unitFourierWeight k (complexShift y x) =
      unitFourierWeight k (complexify x) *
        fourierMonomial (-k) (angleScale n (complexShift y 0)) := by
  rw [unitFourierWeight_eq_monomial, angleScale_shift_split, fourierMonomial_add,
    unitFourierWeight_real]

private theorem scaled_shift_repr_eq {n : ℕ} (y t : RealSpace n) :
    ∃ k : FourierIndex n,
      angleScale n (complexShift y (unitTorusRepr (fun j => (t j : UnitAddCircle)))) =
        angleScale n (complexShift y t) + angleShift k := by
  classical
  have hex : ∀ j : Fin n, ∃ k : ℤ,
      unitTorusRepr (fun j => (t j : UnitAddCircle)) j = t j + k := by
    intro j
    have he : ((unitTorusRepr (fun j => (t j : UnitAddCircle)) j - t j : ℝ) :
        UnitAddCircle) = 0 := by
      simp [unitTorusRepr, AddCircle.coe_equivIoc]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp he
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using hex
  refine ⟨k, ?_⟩
  ext j
  simp [complexShift, angleShift, complexify, hk, mul_add]
  ring

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}

/-- Evaluation on a complex-shifted unit torus at a fixed action. -/
def shiftedTorusValue (f : AnalyticPhaseFunction n G ρ) (p : ComplexSpace n)
    (y : RealSpace n) (t : UnitAddTorus (Fin n)) : ℂ :=
  f.toFun (p, angleScale n (complexShift y (unitTorusRepr t)))

theorem shiftedTorusValue_coe (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ) (t : RealSpace n) :
    f.shiftedTorusValue p y (fun j => (t j : UnitAddCircle)) =
      f.toFun (p, angleScale n (complexShift y t)) := by
  obtain ⟨k, hk⟩ := scaled_shift_repr_eq y t
  unfold shiftedTorusValue
  rw [hk]
  exact f.periodic p hp _ (angleScale_mem_strip (complexShift_mem_strip _ _ hy)) k

theorem continuous_shiftedTorusValue (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ) :
    Continuous (f.shiftedTorusValue p y) := by
  have hquot : IsOpenQuotientMap
      (fun t : RealSpace n => (fun j => (t j : UnitAddCircle))) :=
    IsOpenQuotientMap.piMap (fun _ : Fin n => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hquot.continuous_comp_iff.mp
  have he : f.shiftedTorusValue p y ∘ (fun t : RealSpace n => fun j => (t j : UnitAddCircle)) =
      fun t => f.toFun (p, angleScale n (complexShift y t)) :=
    funext (f.shiftedTorusValue_coe hp y hy)
  rw [he]
  apply f.analytic.continuousOn.comp_continuous
  · apply continuous_const.prodMk
    exact (angleScale n).continuous.comp (by unfold complexShift; fun_prop)
  · intro t
    exact ⟨hp, angleScale_mem_strip (complexShift_mem_strip _ _ hy)⟩

/-- The continuous shifted-torus function used to move the Fourier integration contour. -/
def onShiftedTorus (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ) :
    C(UnitAddTorus (Fin n), ℂ) :=
  ⟨f.shiftedTorusValue p y, f.continuous_shiftedTorusValue hp y hy⟩

theorem fourierCoeff_eq_shifted_unitCube (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n)
    (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ) :
    f.fourierCoeff p k = unitCubeIntegral (fun x =>
      f.toFun (p, angleScale n (complexShift y x)) * unitFourierWeight k (complexShift y x)) := by
  rw [f.fourierCoeff_eq_unitCubeIntegral hp]
  symm
  apply unitCubeIntegral_shift_eq (r := normalizedWidth ρ)
    (f := fun q => f.toFun (p, angleScale n q) * unitFourierWeight k q) (y := y)
  · intro q hq
    have hpair : AnalyticAt ℂ (fun z : ComplexSpace n => (p, angleScale n z)) q :=
      analyticAt_const.prod ((angleScale n).analyticAt q)
    have hfq := f.analytic (p, angleScale n q) ⟨hp, angleScale_mem_strip (ρ := ρ) hq⟩
    exact (hfq.comp (f := fun z : ComplexSpace n => (p, angleScale n z)) hpair).mul
      (analyticAt_unitFourierWeight k q)
  · intro q hq j
    rw [angleScale_update_one, f.periodic p hp _ (angleScale_mem_strip hq),
      unitFourierWeight_periodic]
  · exact hy

theorem shiftedCoeff_eq_unitCube (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (y : RealSpace n)
    (hy : ∀ j, |y j| ≤ normalizedWidth ρ) (k : FourierIndex n) :
    UnitAddTorus.mFourierCoeff (f.shiftedTorusValue p y) k = unitCubeIntegral (fun x =>
      f.toFun (p, angleScale n (complexShift y x)) * unitFourierWeight k (complexify x)) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : RealSpace n)]
  unfold unitCubeIntegral
  rw [unitCubeMeasure_eq_restrict_Ioc]
  simp only [Pi.zero_apply, zero_add]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [f.shiftedTorusValue_coe hp y hy, smul_eq_mul, mFourier_eq_fourierMonomial,
    unitFourierWeight_real, mul_comm]

theorem shiftedCoeff_eq (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ) (k : FourierIndex n) :
    UnitAddTorus.mFourierCoeff (f.shiftedTorusValue p y) k =
      f.fourierCoeff p k * fourierMonomial k (angleScale n (complexShift y 0)) := by
  have he := f.fourierCoeff_eq_shifted_unitCube hp k y hy
  simp_rw [unitFourierWeight_shift_split, ← mul_assoc] at he
  unfold unitCubeIntegral at he
  rw [integral_mul_const] at he
  have hg := f.shiftedCoeff_eq_unitCube hp y hy k
  unfold unitCubeIntegral at hg
  rw [← hg] at he
  rw [he, mul_assoc, fourierMonomial_neg_mul, mul_one]

theorem hasSum_fourier_shifted (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (y : RealSpace n) (hy : ∀ j, |y j| ≤ normalizedWidth ρ)
    {δ : ℝ} (hδ : 0 < δ)
    (hwidth : ‖imagPart (angleScale n (complexShift y 0))‖ ≤ (ρ : ℝ) - δ)
    (t : RealSpace n) :
    HasSum (fun k => f.fourierCoeff p k * fourierMonomial k (angleScale n (complexShift y t)))
      (f.toFun (p, angleScale n (complexShift y t))) := by
  have hsum : Summable (UnitAddTorus.mFourierCoeff (f.shiftedTorusValue p y)) := by
    apply ((summable_exp_indexLength n hδ).mul_left f.uniformNorm).of_norm_bounded
    intro k
    rw [f.shiftedCoeff_eq hp y hy]
    simpa only [neg_mul, mul_comm] using norm_fourierTerm_le
      (f.norm_le_iff.mp le_rfl).nonneg (f.norm_fourierCoeff_le_exp hp) hwidth k
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := f.onShiftedTorus hp y hy) hsum (fun j => (t j : UnitAddCircle))
  simp only [onShiftedTorus, ContinuousMap.coe_mk, f.shiftedCoeff_eq hp y hy,
    smul_eq_mul, mFourier_eq_fourierMonomial, f.shiftedTorusValue_coe hp y hy] at hs
  convert hs using 1
  funext k
  rw [angleScale_shift_split, fourierMonomial_add]
  ring

end AnalyticPhaseFunction
end KamProject.Arnold1963
