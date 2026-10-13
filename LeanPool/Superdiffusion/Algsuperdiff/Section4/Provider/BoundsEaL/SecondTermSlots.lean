/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeFirstThird
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.SecondTermArithmetic

/-!
# SecondTermSlots

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's second summand: the slots it reads, and their moments

## What this module supplies

The S summand of `MajorantSlots.step3DisplayAt` is the one Step 5 handles "with
additional inputs".  Before its `p/2`-moment can be written down, three slot
facts are needed that the proved layer does not yet carry:

* the two-term `ℝ≥0∞` Minkowski step in the development normal form
  (`lintegral_rpow_real_add_le_of_moments`), for a SUM of two real observables;
* the `L`-free VALUE slot's own moment, i.e. bullet (B6b) with its two legs --
  the `L∞` leg of `ValueSlotLinfty` and the mean-value tail of
  `ValueSlotMoment` -- summed (`lintegral_rpow_lFreeValueSlot_le`).
* the a.e. measurability of the three named summands of `step3DisplayAt`
  separately, which is what `PerCubeSixWay`'s six-way split asks for at the
  untouched sample.

Everything here is either a proved bullet read at a new exponent or generic
measure theory; no `γ`-power, no `s`-power and no parameter range is moved.

## References

* ABK26, `l.bounds.mathcal.E.aL`, bullet (B6b), Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Two-term Minkowski in the development normal form -/

/-- The development normal form, after the `q`-th root.  Local re-derivation
(distinct name) of `PerCubeSixWay`'s `private rootLe_of_moment`. -/
private theorem rootLeMomentTwo {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F : Omega → ℝ≥0∞} {Rv q : ℝ} (hq0 : 0 < q)
    (h : (∫⁻ omega, F omega ^ q ∂mu) ≤ ENNReal.ofReal Rv ^ q) :
    (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal Rv := by
  refine le_trans (ENNReal.rpow_le_rpow h (one_div_nonneg.mpr hq0.le)) (le_of_eq ?_)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]

/-- The two-function `ℝ≥0∞` Minkowski inequality, in applied form.  Disclosed
re-derivation (distinct name) of `PerCubeSixWay`'s `private rootAdd`. -/
private theorem rootAddTwo {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {q : ℝ} (hq : 1 ≤ q) {F G : Omega → ℝ≥0∞} (hF : AEMeasurable F mu)
    (hG : AEMeasurable G mu) :
    (∫⁻ omega, (F omega + G omega) ^ q ∂mu) ^ (1 / q) ≤
      (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) + (∫⁻ omega, G omega ^ q ∂mu) ^ (1 / q) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := mu) (f := F) (g := G) hF hG hq
  simp only [Pi.add_apply] at h
  exact h

/-- **The two-term Minkowski step observables**, in the development normal form `∫⁻
(ofReal ·)^q ≤ (ofReal R)^q`. -/
theorem lintegral_rpow_real_add_le_of_moments {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F G : Omega → ℝ} {RF RG q : ℝ} (hq : 1 ≤ q)
    (hFm : AEMeasurable F mu) (hGm : AEMeasurable G mu) (hRF : 0 ≤ RF) (hRG : 0 ≤ RG)
    (hF : (∫⁻ omega, ENNReal.ofReal (F omega) ^ q ∂mu) ≤ ENNReal.ofReal RF ^ q)
    (hG : (∫⁻ omega, ENNReal.ofReal (G omega) ^ q ∂mu) ≤ ENNReal.ofReal RG ^ q) :
    (∫⁻ omega, ENNReal.ofReal (F omega + G omega) ^ q ∂mu) ≤
      ENNReal.ofReal (RF + RG) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmono : (∫⁻ omega, ENNReal.ofReal (F omega + G omega) ^ q ∂mu) ≤
      ∫⁻ omega, (ENNReal.ofReal (F omega) + ENNReal.ofReal (G omega)) ^ q ∂mu :=
    lintegral_mono fun omega => ENNReal.rpow_le_rpow ENNReal.ofReal_add_le hq0.le
  have hroot : (∫⁻ omega, (ENNReal.ofReal (F omega) + ENNReal.ofReal (G omega)) ^ q ∂mu) ^
      (1 / q) ≤ ENNReal.ofReal (RF + RG) := by
    refine le_trans (rootAddTwo hq hFm.ennreal_ofReal hGm.ennreal_ofReal) ?_
    refine le_trans (add_le_add (rootLeMomentTwo hq0 hF) (rootLeMomentTwo hq0 hG))
      (le_of_eq ?_)
    rw [ENNReal.ofReal_add hRF hRG]
  have hraise := ENNReal.rpow_le_rpow hroot hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one] at hraise
  exact le_trans hmono hraise

/-! ## 2. The `L`-free value slot: nonnegativity, measurability, moment -/

/-- The `L`-free value slot is nonnegative at the canonical tail gauge. -/
theorem lFreeValueSlot_tailSeriesGauge_nonneg (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ lFreeValueSlot m (tailSeriesGauge m) R omega := by
  refine add_nonneg (Cutoff.localCubeControl_nonneg R.scale _) ?_
  refine mul_nonneg (centeringConst_nonneg d) (mul_nonneg (by positivity) ?_)
  exact tsum_nonneg fun i => tailLayerTerm_nonneg m m (0 : Fin d → ℤ) omega i

/-- **The value slot's majorant at moment `r`**: the two legs of bullet (B6b),
summed. -/
def valueSlotMajorant (M : ABKModel d) (m j : ℤ) (r : ℝ) : ℝ :=
  gammaTwoMomentBound r (valueLinftyConst d *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))) +
    gammaTwoMomentBound r (centeringConst d *
      (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ))))

theorem valueSlotMajorant_nonneg (M : ABKModel d) (m j : ℤ) (r : ℝ) :
    0 ≤ valueSlotMajorant M m j r := by
  have hmin : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1 : (0 : ℝ) ≤ valueLinftyConst d *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    refine mul_nonneg (mul_nonneg (valueLinftyConst_nonneg d) (by linarith only [hmin])) ?_
    exact Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ centeringConst d * (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ))) :=
    mul_nonneg (centeringConst_nonneg d)
      (mul_nonneg (deepGradConst_pos M).le (Real.rpow_nonneg (by norm_num) _))
  exact add_nonneg (gammaTwoMomentBound_nonneg h1) (gammaTwoMomentBound_nonneg h2)

/-- **Bullet (B6b), both legs, at every moment `r ∈ [1,∞)`.**

The `L`-free value slot is the sum of the `L∞` leg and the mean-value tail, so
`ℝ≥0∞` Minkowski gives its moment as the sum of the two proved ones.  This is
the form Step 5's second summand consumes. -/
theorem lintegral_rpow_lFreeValueSlot_le (M : ABKModel d) {m : ℤ} (R : TriadicCube d)
    (hjm : R.scale ≤ m) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (lFreeValueSlot m (tailSeriesGauge m) R omega) ^ r
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (valueSlotMajorant M m R.scale r) ^ r := by
  have hmin : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hL0 : (0 : ℝ) ≤ gammaTwoMomentBound r (valueLinftyConst d *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    refine gammaTwoMomentBound_nonneg ?_
    refine mul_nonneg (mul_nonneg (valueLinftyConst_nonneg d) (by linarith only [hmin])) ?_
    exact Real.rpow_nonneg (by norm_num) _
  have hT0 : (0 : ℝ) ≤ gammaTwoMomentBound r (centeringConst d *
      (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ)))) := by
    refine gammaTwoMomentBound_nonneg (mul_nonneg (centeringConst_nonneg d) ?_)
    exact mul_nonneg (deepGradConst_pos M).le (Real.rpow_nonneg (by norm_num) _)
  have hLm : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      Cutoff.localCubeControl R.scale
        (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
          (shellIncrement omega.1 (R.scale - 2) m))) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (((Cutoff.measurable_localCubeControl R.scale).comp
      ((ShellField.measurable_translate
          (Support.triadicLatticePoint R.scale R.index)).comp
        (measurable_shellIncrement_cutoffSample (R.scale - 2) m)))).aemeasurable
  have hTm : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      centeringConst d * ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (((measurable_tailSeriesGauge m m (0 : Fin d → ℤ)).const_mul _).const_mul _).aemeasurable
  have hkey := lintegral_rpow_real_add_le_of_moments
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure) hr hLm hTm hL0 hT0
    (lintegral_rpow_valueSlotLinfty_le M R hjm hr)
    (lintegral_rpow_valueSlotMeanValueTail_le M m hr)
  have hval : ∀ omega : Cutoff.CutoffSample d,
      lFreeValueSlot m (tailSeriesGauge m) R omega =
        Cutoff.localCubeControl R.scale
            (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
              (shellIncrement omega.1 (R.scale - 2) m)) +
          centeringConst d *
            ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega) := fun omega =>
    lFreeValueSlot_eq_linfty_add_meanValueTail m R omega
  have hcong : (∫⁻ omega : Cutoff.CutoffSample d,
      ENNReal.ofReal (lFreeValueSlot m (tailSeriesGauge m) R omega) ^ r
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Cutoff.localCubeControl R.scale
            (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
              (shellIncrement omega.1 (R.scale - 2) m)) +
          centeringConst d *
            ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega)) ^ r
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    lintegral_congr fun omega => by rw [hval omega]
  rw [hcong, valueSlotMajorant]
  exact hkey

/-! ## 3. The three summands are a.e. measurable -/

/-- The `λ`-slot and the two shell slots, packaged: the a.e. measurability
ingredients every summand of `step3DisplayAt` is built from. -/
theorem slotMeasurableTriple (M : ABKModel d) (m : ℤ) (R : TriadicCube d) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        lFreeGradSlot m (tailSeriesGauge m) R omega) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        lFreeValueSlot m (tailSeriesGauge m) R omega)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  ⟨(measurable_inv_unitCubeLambda_twoGamma M R).aemeasurable,
    (measurable_lFreeGradSlot m (tailSeriesGauge m)
      (fun k v => measurable_tailSeriesGauge m k v) R).aemeasurable,
    (measurable_lFreeValueSlot m (tailSeriesGauge m)
      (fun k v => measurable_tailSeriesGauge m k v) R).aemeasurable⟩

/-- The bracket at an arbitrary nonnegative exponent is a.e. measurable. -/
theorem aemeasurable_step3Bracket [NeZero d] (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    {theta : ℝ} (hth : 0 ≤ theta) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        Real.rpow (1 + lFreeGradSlot m (tailSeriesGauge m) R omega *
          (unitCubeLambda (2 * M.gamma) (.finite 2)
            (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) theta)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨hlam, hgrad, -⟩ := slotMeasurableTriple M m R
  exact (Real.continuous_rpow_const hth).measurable.comp_aemeasurable
    ((hgrad.mul hlam).const_add 1)

/-- **The summand is a.e. measurable.** -/
theorem aemeasurable_step3FirstTerm [NeZero d] (M : ABKModel d) (Cd : ℝ) (m : ℤ)
    (R : TriadicCube d) {s : ℝ} (hs : 0 < s) (hgam : M.gamma ≤ 1 / 8) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        step3FirstTerm Cd M m R omega s (lFreeGradSlot m (tailSeriesGauge m) R omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hden : (0 : ℝ) < 1 - 4 * M.gamma := by linarith only [hgam]
  have hth : (0 : ℝ) ≤ 2 * s / (1 - 4 * M.gamma) :=
    div_nonneg (by linarith only [hs]) hden.le
  have hbr := aemeasurable_step3Bracket M m R hth
  have herr := aemeasurable_unitCubeHomogenizationError22_unitRescaledCutoffCoeff M R ⟨s, hs⟩
  exact ((hbr.const_mul _).mul (herr.pow_const 2))

/-- **The S summand is a.e. measurable.** -/
theorem aemeasurable_step3SecondTerm [NeZero d] (M : ABKModel d) (Cd : ℝ) (m : ℤ)
    (R : TriadicCube d) (hgam : M.gamma ≤ 1 / 8) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        step3SecondTerm Cd M m R omega (lFreeGradSlot m (tailSeriesGauge m) R omega)
          (lFreeValueSlot m (tailSeriesGauge m) R omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hden : (0 : ℝ) < 1 - 4 * M.gamma := by linarith only [hgam]
  have hth : (0 : ℝ) ≤ 4 * M.gamma / (1 - 4 * M.gamma) :=
    div_nonneg (by linarith only [hgam0]) hden.le
  obtain ⟨hlam, -, hval⟩ := slotMeasurableTriple M m R
  have hbr := aemeasurable_step3Bracket M m R hth
  exact ((((hlam.const_mul _).mul hbr)).mul (((hval.pow_const 2).const_mul _).add_const _))

/-- **The third summand is a.e. measurable.** -/
theorem aemeasurable_step3ThirdTerm [NeZero d] (M : ABKModel d) (Cd : ℝ) (m : ℤ)
    (R : TriadicCube d) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        step3ThirdTerm Cd M m R omega (lFreeGradSlot m (tailSeriesGauge m) R omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨hlam, hgrad, -⟩ := slotMeasurableTriple M m R
  exact (((hlam.const_add _).mul hgrad).pow_const 2).const_mul _

end

end Algsuperdiff.Section4.Provider.BoundsEaL
