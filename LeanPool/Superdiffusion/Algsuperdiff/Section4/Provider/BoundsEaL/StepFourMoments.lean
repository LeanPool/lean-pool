/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentEngine
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.StepFourSigmaBar
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.ErrorSlotB4
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.GradBottomLayer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.ValueSlotLinfty

/-!
# StepFourMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 4's "hence, for every `q`": the moment reading of the proved bullets

## What this module does

Step 4 of the proof of `l.bounds.mathcal.E.aL` lists the inputs of the
sensitivity display and converts each into a `q`-th moment bound.

The bullet table, and where each conversion is:

* (B1) `σ_m^{-1}σ_{j−2} ≤ 4`, deterministic:
  `exists_lintegral_rpow_inv_sigmaBar_mul_sigmaBar_sub_two_le`.
* (B2) `(σ_mσ_{j−2}^{-1}−1)² ≤ …`, deterministic:
  `exists_lintegral_rpow_sigmaBar_ratio_sub_one_sq_le`.
* (B3) `3^{γj}σ_{j−2}^{-1} ≤ 4c⋆^{-1/2}γ^{1/2}`, deterministic:
  `exists_lintegral_rpow_gamma_weight_inv_sigmaBar_le`.
* (B4) `𝓔_{s,2,2}(□_j;𝐚_{j−2},σ_{j−2})`, `(Γ₂,Γ_{1/2})`:
  `exists_lintegral_rpow_unitCubeHomogenizationError22_le`.
* (B5) `λ_{γ,2}^{-1}(□_j;𝐚_{j−2})`, `Γ_{1/3}`: NOT here -- see
  `LambdaSlotB5.lean`.
* (B6a) `3^{2j}‖∇(k_L−k_{j−2})‖_{W^{1,∞}}`, `Γ₂`:
  `lintegral_rpow_weightedFullGradSeries_le`,
  `lintegral_rpow_lFreeGradSlot_le`.
* (B6b) `‖k_L−k_{j−2}−(k_L−k_m)_{□_m}‖_{L²}`, `Γ₂`:
  `lintegral_rpow_valueSlotLinfty_le` and
  `lintegral_rpow_valueSlotMeanValueTail_le` (the two legs, kept apart).

The three deterministic bullets convert trivially: a probability measure has
total mass one, so the `q`-th moment of a constant is the constant.  The four
random ones convert through `l.moments.gamma.psi`, whose `q^{1/σ}` is `√q` at
`σ = 2` (the printed `q^{1/2}`, and the anchor's `√p`) and `q²` at `σ = 1/2`
(the printed `q²`).

## What is NOT claimed

The two `q`-powers are exactly the printed ones and no exponent is moved; the
constants are the explicit ones of the proved displays, which the manuscript's
`C(d, c⋆)` convention absorbs.

## References

* ABK26, `l.bounds.mathcal.E.aL`; `l.moments.gamma.psi`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The three deterministic bullets -/

/-! ## 2. (B4): the two-term bullet at the literal `(2,2)` error -/

/-- **(B4) at every moment `q ∈ [1,∞)`, for the literal `(2,2)` error.**

The printed conversion is `E[𝓔_{s,2,2}^q]^{1/q} ≤ C s^{-1} q^{1/2} γ^{1/2} + C
q² exp(−C^{-1}γ^{-1})`: the `√q` is the `Γ₂` lane's `q^{1/σ}` at `σ = 2` and
the `q²` is the `Γ_{1/2}` lane's at `σ = 1/2`.  Both are carried verbatim by
`gammaTwoHalfMomentBound`. -/
theorem exists_lintegral_rpow_unitCubeHomogenizationError22_le (d : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : ℝ, ∀ _hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
          ∀ R : TriadicCube d, ∀ p : ℝ, 1 ≤ p →
            ∫⁻ omega : Cutoff.CutoffSample d,
                ENNReal.ofReal
                  (Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError s
                    (.finite 2) (.finite 2)
                    (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
                    (Observable.isotropicComparatorMatrix
                      (Annealed.sigmaBar M (R.scale - 2)))) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure
              ≤ ENNReal.ofReal (gammaTwoHalfMomentBound p
                  (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
                    (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))
                  (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
                    Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))))) ^ p  := by
  obtain ⟨C, hC0, hall⟩ :=
    exists_isTwoTermBigOWith_annularErrorObservable_translate d
  refine ⟨C, hC0, fun M hreg s hsWindow R p hp => ?_⟩
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hsWindow.1
  have hae := ae_eq_annularErrorObservable_translate M R ⟨s, hs0⟩
  refine lintegral_rpow_le_of_twoTerm_gammaTwoHalf hp
    (fun omega => Support.annularErrorObservable_nonneg M R.scale ⟨s, hs0⟩ _)
    (hall M hreg s hsWindow R) ?_ le_rfl
  filter_upwards [hae] with omega homega
  exact le_of_eq (congrArg ENNReal.ofReal homega)

/-! ## 3. (B6a): the whole `L`-free gradient slot -/

/-- Countable nonnegative `ℕ`-sums of measurable real functions are measurable.
Local re-derivation (distinct name) of the `private` helpers named in the
module docstring. -/
private theorem measurable_tsum_nat_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (term : ℕ → Omega → ℝ) (hmeas : ∀ n, Measurable (term n))
    (hnonneg : ∀ n omega, 0 ≤ term n omega) :
    Measurable fun omega => ∑' n : ℕ, term n omega := by
  have hnn : Measurable (fun omega => ∑' n : ℕ, (term n omega).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hmeas n).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  refine tsum_congr fun n => ?_
  rw [Real.toNNReal_of_nonneg (hnonneg n omega)]
  rfl

theorem fullGradSeries_nonneg (k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ fullGradSeries k v omega :=
  tsum_nonneg fun n => gradLayerGauge_nonneg k v omega (k - 1 + (n : ℤ))

theorem measurable_fullGradSeries (k : ℤ) (v : Fin d → ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => fullGradSeries k v omega :=
  measurable_tsum_nat_of_nonneg _
    (fun n => measurable_gradLayerGauge k v (k - 1 + (n : ℤ)))
    (fun n omega => gradLayerGauge_nonneg k v omega (k - 1 + (n : ℤ)))

/-- **(B6a) at the slot itself.**  Almost surely the `L`-free gradient slot IS
the weighted full series, so it inherits the moment bound.  This is the form the
Step-5 assembly consumes. -/
theorem lintegral_rpow_lFreeGradSlot_le (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (hkm : R.scale ≤ m) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (lFreeGradSlot m (tailSeriesGauge m) R omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (gammaTwoMomentBound p
          (fullGradConst M * Real.rpow 3 (M.gamma * (R.scale : ℝ)))) ^ p := by
  have hA : (0 : ℝ) < fullGradConst M * Real.rpow 3 (M.gamma * (R.scale : ℝ)) :=
    mul_pos (fullGradConst_pos M) (Real.rpow_pos_of_pos (by norm_num) _)
  refine lintegral_rpow_le_of_isBigOWith_gammaTwo hA hp
    (fun omega => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (fullGradSeries_nonneg R.scale R.index omega))
    ((measurable_fullGradSeries R.scale R.index).const_mul _).aemeasurable
    (isBigOWith_gammaSigma_weightedFullGradSeries M R.scale R.index) ?_ le_rfl
  filter_upwards [ae_lFreeGradSlot_eq_weighted_fullGradSeries M m R hkm] with omega homega
  exact le_of_eq (congrArg ENNReal.ofReal homega)

/-! ## 4. (B6b): the two legs of the `L`-free value slot -/

theorem valueLinftyConst_pos (hd : 0 < d) : 0 < valueLinftyConst d := by
  have hlog : (0 : ℝ) < largeCubeLogConst := largeCubeLogConst_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsq : (0 : ℝ) < Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hstream : (0 : ℝ) < streamLinftyConst d := streamLinftyConst_pos hd
  rw [valueLinftyConst]
  positivity

/-- **(B6b), the `L∞` leg, at every moment `q ∈ [1,∞)`.** -/
theorem lintegral_rpow_valueSlotLinfty_le (M : ABKModel d) {m : ℤ}
    (R : TriadicCube d) (hjm : R.scale ≤ m) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Cutoff.localCubeControl R.scale
          (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
            (shellIncrement omega.1 (R.scale - 2) m))) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (gammaTwoMomentBound p
          (valueLinftyConst d *
            (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)))) ^ p := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hmin : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA : (0 : ℝ) < valueLinftyConst d *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    have h1 : (0 : ℝ) < valueLinftyConst d := valueLinftyConst_pos hd
    have h2 : (0 : ℝ) < 1 + min (Real.sqrt M.gamma⁻¹)
        (Real.sqrt ((m : ℝ) - (R.scale : ℝ))) := by linarith only [hmin]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hmeas : Measurable fun omega : Cutoff.CutoffSample d =>
      Cutoff.localCubeControl R.scale
        (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
          (shellIncrement omega.1 (R.scale - 2) m)) :=
    (Cutoff.measurable_localCubeControl R.scale).comp
      ((ShellField.measurable_translate
          (Support.triadicLatticePoint R.scale R.index)).comp
        (measurable_shellIncrement_cutoffSample (R.scale - 2) m))
  exact lintegral_ofReal_rpow_le_of_isBigOWith_gammaTwo hA hp
    (fun omega => Cutoff.localCubeControl_nonneg R.scale _) hmeas.aemeasurable
    (isBigOWith_gammaSigma_valueSlotLinfty M R hjm) le_rfl

/-- **(B6b), the mean-value leg, at every moment `q ∈ [1,∞)`.**

The two legs are deliberately NOT summed: Step 5 wants them separate. -/
theorem lintegral_rpow_valueSlotMeanValueTail_le (M : ABKModel d) (m : ℤ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (centeringConst d *
          ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega)) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (gammaTwoMomentBound p
          (centeringConst d *
            (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ))))) ^ p := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcent : (0 : ℝ) < centeringConst d := by
    rw [centeringConst]
    positivity
  have hA : (0 : ℝ) < centeringConst d *
      (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ))) :=
    mul_pos hcent (mul_pos (deepGradConst_pos M)
      (Real.rpow_pos_of_pos (by norm_num) _))
  have hnn : ∀ omega : Cutoff.CutoffSample d, (0 : ℝ) ≤ centeringConst d *
      ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega) := by
    intro omega
    refine mul_nonneg (centeringConst_nonneg d) (mul_nonneg (by positivity) ?_)
    exact tsum_nonneg fun i => tailLayerTerm_nonneg m m (0 : Fin d → ℤ) omega i
  have hmeas : Measurable fun omega : Cutoff.CutoffSample d =>
      centeringConst d *
        ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega) :=
    ((measurable_tailSeriesGauge m m (0 : Fin d → ℤ)).const_mul _).const_mul _
  exact lintegral_ofReal_rpow_le_of_isBigOWith_gammaTwo hA hp hnn hmeas.aemeasurable
    (isBigOWith_gammaSigma_valueSlotMeanValueTail M m) le_rfl

end

end Algsuperdiff.Section4.Provider.BoundsEaL
