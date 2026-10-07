/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildStokesLinear
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong time continuity of the regularized Stokes operator

The Fourier multiplier for the Stokes operator is strongly continuous at
positive elapsed times, as used in `lem:reg-local-mild`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The Fourier-side vector field obtained by applying the Stokes formula at each frequency. -/
@[expose]
def stokesFormulaField (t : ℝ) (F : ComplexTensorL2) : L2Vec3 → ComplexVec3 :=
  fun ξ => stokesApplyFormula t ξ (F ξ)

private theorem stokesFormulaField_memLp {t : ℝ} (ht : 0 < t)
    (F : ComplexTensorL2) : MemLp (stokesFormulaField t F) 2 volume := by
  let g := stokesFourierMultiplier ht F
  have hformula := measurableFourierMultiplier_ae_eq
    (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
    (stokesApplyFormula_measurable t)
    (1 / Real.sqrt (2 * Real.exp 1 * t))
    (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) F
  have hEq : stokesFormulaField t F =ᵐ[volume] g := by
    filter_upwards [hformula] with ξ hξ
    simpa [stokesFormulaField, g, stokesFourierMultiplier] using hξ.symm
  exact MemLp.ae_eq hEq.symm (Lp.memLp g)

private theorem stokesFormulaField_aestronglyMeasurable {t : ℝ} (ht : 0 < t)
    (F : ComplexTensorL2) : AEStronglyMeasurable (stokesFormulaField t F) volume :=
  (stokesFormulaField_memLp ht F).aestronglyMeasurable

/-- The frequency-side Stokes multiplier is strongly continuous on each
fixed tensor input at positive elapsed times. -/
theorem stokesFourierMultiplier_continuousAt {t₀ : ℝ} (ht₀ : 0 < t₀)
    (F : ComplexTensorL2) :
    ContinuousAt (fun t : {t : ℝ // 0 < t} => stokesFourierMultiplier t.2 F)
      ⟨t₀, ht₀⟩ := by
  let q₀ : {t : ℝ // 0 < t} := ⟨t₀, ht₀⟩
  let Φ : {t : ℝ // 0 < t} → L2Vec3 → ComplexVec3 :=
    fun q => stokesFormulaField q.1 F
  let f₀ : L2Vec3 → ComplexVec3 := Φ q₀
  have hFmeas : AEStronglyMeasurable F volume := (Lp.memLp F).aestronglyMeasurable
  have hFpow : Integrable (fun ξ : L2Vec3 => ‖F ξ‖ ^ 2) volume :=
    (Lp.memLp F).integrable_norm_pow (by norm_num)
  have hformulaLp (q : {t : ℝ // 0 < t}) :
      (stokesFormulaField q.1 F) =ᵐ[volume] stokesFourierMultiplier q.2 F := by
    let g := stokesFourierMultiplier q.2 F
    have hformula := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula q.1 p.1 p.2)
      (stokesApplyFormula_measurable q.1)
      (1 / Real.sqrt (2 * Real.exp 1 * q.1))
      (by intro ξ T; exact stokesApplyFormula_norm_le q.2 ξ T) F
    filter_upwards [hformula] with ξ hξ
    simpa [stokesFormulaField, g, stokesFourierMultiplier] using hξ.symm
  have hMem (q : {t : ℝ // 0 < t}) : MemLp (Φ q) 2 volume :=
    stokesFormulaField_memLp q.2 F
  have hIntegral : Tendsto
      (fun q : {t : ℝ // 0 < t} =>
        ∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)
      (𝓝 q₀) (𝓝 0) := by
    let B : ℝ := 1 / Real.sqrt (Real.exp 1 * t₀)
    let bound : L2Vec3 → ℝ := fun ξ => (2 * B * ‖F ξ‖) ^ 2
    have hB : 0 < B := by positivity
    have hboundInt : Integrable bound volume := by
      have hmul := hFpow.const_mul ((2 * B) ^ 2)
      convert hmul using 1
      ext ξ
      simp [bound, mul_pow, mul_assoc]
    have hqLower : ∀ᶠ q : {t : ℝ // 0 < t} in 𝓝 q₀, t₀ / 2 < q.1 := by
      have hopen : Set.Ioi (t₀ / 2) ∈ 𝓝 t₀ := Ioi_mem_nhds (by linarith only [ht₀])
      have hval : Tendsto (fun q : {t : ℝ // 0 < t} => (q : ℝ))
          (𝓝 q₀) (𝓝 t₀) := by
        simpa [q₀] using
          (continuous_subtype_val.continuousAt.tendsto :
            Tendsto (fun q : {t : ℝ // 0 < t} => (q : ℝ))
              (𝓝 (⟨t₀, ht₀⟩ : {t : ℝ // 0 < t})) (𝓝 t₀))
      have heventually := hval.eventually_mem hopen
      simpa [q₀] using heventually
    have hDCT : Tendsto
        (fun q : {t : ℝ // 0 < t} =>
          ∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)
        (𝓝 q₀) (𝓝 (∫ _ξ : L2Vec3, (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 q₀)
        (F := fun q ξ => ‖Φ q ξ - f₀ ξ‖ ^ 2)
        (f := fun _ : L2Vec3 => (0 : ℝ)) bound ?_ ?_ hboundInt ?_
      · filter_upwards [] with q
        have hq := stokesFormulaField_aestronglyMeasurable q.2 F
        exact (continuous_norm.pow 2).comp_aestronglyMeasurable
          (hq.sub (stokesFormulaField_aestronglyMeasurable ht₀ F))
      · filter_upwards [hqLower] with q hq
        exact Filter.Eventually.of_forall fun ξ => by
          have hcoef : 1 / Real.sqrt (2 * Real.exp 1 * q.1) ≤ B := by
            dsimp [B]
            apply one_div_le_one_div_of_le
            · positivity
            · apply Real.sqrt_le_sqrt
              nlinarith only [hq, Real.exp_pos (1 : ℝ)]
          have hqbound := stokesApplyFormula_norm_le q.2 ξ (F ξ)
          have h0bound := stokesApplyFormula_norm_le ht₀ ξ (F ξ)
          have hq' : ‖Φ q ξ‖ ≤ B * ‖F ξ‖ := by
            simpa [Φ, stokesFormulaField] using hqbound.trans
              (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (F ξ)))
          have h0' : ‖f₀ ξ‖ ≤ B * ‖F ξ‖ := by
            have hq₀ : t₀ / 2 < (q₀ : ℝ) := by
              dsimp [q₀]
              nlinarith only [ht₀]
            have hcoef₀ : 1 / Real.sqrt (2 * Real.exp 1 * (q₀ : ℝ)) ≤ B := by
              dsimp [B]
              apply one_div_le_one_div_of_le
              · positivity
              · apply Real.sqrt_le_sqrt
                nlinarith only [hq₀, Real.exp_pos (1 : ℝ)]
            simpa [f₀, Φ, q₀, stokesFormulaField] using h0bound.trans
              (mul_le_mul_of_nonneg_right hcoef₀ (norm_nonneg (F ξ)))
          have hnormBound : ‖Φ q ξ - f₀ ξ‖ ≤ 2 * B * ‖F ξ‖ := by
            calc
              ‖Φ q ξ - f₀ ξ‖ ≤ ‖Φ q ξ‖ + ‖f₀ ξ‖ := norm_sub_le _ _
              _ ≤ B * ‖F ξ‖ + B * ‖F ξ‖ := add_le_add hq' h0'
              _ = 2 * B * ‖F ξ‖ := by ring
          have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnormBound
          have hsqNonneg : 0 ≤ (‖Φ q ξ - f₀ ξ‖ : ℝ) ^ 2 := sq_nonneg _
          simpa [Real.norm_eq_abs, abs_of_nonneg hsqNonneg, bound] using hsq
      · filter_upwards [] with ξ
        have hformula : Tendsto (fun q : {t : ℝ // 0 < t} => Φ q ξ)
            (𝓝 q₀) (𝓝 (f₀ ξ)) := by
          have hcont : Continuous (fun t : ℝ => stokesApplyFormula t ξ (F ξ)) := by
            fun_prop [stokesApplyFormula, heatSymbol]
          simpa [Φ, f₀, stokesFormulaField, q₀, Function.comp_def] using
            hcont.continuousAt.tendsto.comp continuous_subtype_val.continuousAt.tendsto
        have hdiff : Tendsto (fun q : {t : ℝ // 0 < t} => Φ q ξ - f₀ ξ)
            (𝓝 q₀) (𝓝 0) := by
          have hconst : Tendsto (fun _ : {t : ℝ // 0 < t} => f₀ ξ)
              (𝓝 q₀) (𝓝 (f₀ ξ)) := tendsto_const_nhds
          simpa [Φ] using hformula.sub hconst
        have hnorm := (continuous_norm.continuousAt.tendsto.comp hdiff)
        have hpow := (continuousAt_id.pow 2).tendsto.comp hnorm
        simpa [Φ, f₀, q₀, sub_self, Function.comp_def] using hpow
    simpa [integral_zero] using hDCT
  have hLpTendsto : Tendsto
      (fun q : {t : ℝ // 0 < t} => (hMem q).toLp (Φ q))
      (𝓝 q₀) (𝓝 ((hMem q₀).toLp f₀)) := by
    -- The integral convergence above gives convergence of the square-root norm.
    have hroot : Tendsto
        (fun q : {t : ℝ // 0 < t} =>
          Real.sqrt (∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2))
        (𝓝 q₀) (𝓝 0) := by
      simpa [Function.comp_def] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hIntegral)
    have hnorm : Tendsto
        (fun q : {t : ℝ // 0 < t} => eLpNorm (Φ q - f₀) 2 volume)
        (𝓝 q₀) (𝓝 0) := by
      have hformulaNorm (q : {t : ℝ // 0 < t}) :
          eLpNorm (Φ q - f₀) 2 volume =
            ENNReal.ofReal (Real.sqrt (∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)) := by
        rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
          ((hMem q).sub (hMem q₀))]
        simp only [ENNReal.toReal_ofNat]
        congr 1
        rw [Real.sqrt_eq_rpow]
        norm_num
        simp [f₀]
      rw [Filter.tendsto_congr' (Filter.Eventually.of_forall hformulaNorm)]
      simpa using ENNReal.tendsto_ofReal hroot
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Φ hMem f₀ (hMem q₀)).2 hnorm
  have hformulaToLp : ∀ q : {t : ℝ // 0 < t},
      (hMem q).toLp (Φ q) = stokesFourierMultiplier q.2 F := by
    intro q
    apply Lp.ext
    exact (hMem q).coeFn_toLp.trans (hformulaLp q)
  have hLpTendsto' : Tendsto
      (fun q : {t : ℝ // 0 < t} => stokesFourierMultiplier q.2 F)
      (𝓝 q₀) (𝓝 (stokesFourierMultiplier ht₀ F)) := by
    have hEnd : (hMem q₀).toLp f₀ = stokesFourierMultiplier ht₀ F := by
      simpa [f₀] using hformulaToLp q₀
    simpa only [hformulaToLp, hEnd] using hLpTendsto
  exact hLpTendsto'

/-- The physical real Stokes operator is strongly continuous at positive
elapsed times. -/
theorem realStokesOperator_continuousAt {t₀ : ℝ} (ht₀ : 0 < t₀)
    (F : RealTensorL2) :
    ContinuousAt (fun t : {t : ℝ // 0 < t} => realStokesOperator t.2 F)
      ⟨t₀, ht₀⟩ := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  let cF := complexifyTensorL2 F
  have hcomplex := stokesFourierMultiplier_continuousAt ht₀ (ℱT cF)
  have hstokes : ContinuousAt
      (fun t : {t : ℝ // 0 < t} =>
        ℱV.symm (stokesFourierMultiplier t.2 (ℱT cF))) ⟨t₀, ht₀⟩ :=
    ℱV.symm.continuous.continuousAt.comp hcomplex
  have hreal := realPartVectorL2.continuous.continuousAt.comp hstokes
  have hmapEq : (fun t : {t : ℝ // 0 < t} =>
      realPartVectorL2 (ℱV.symm (stokesFourierMultiplier t.2 (ℱT cF)))) =
        realPartVectorL2 ∘ (fun t : {t : ℝ // 0 < t} =>
          ℱV.symm (stokesFourierMultiplier t.2 (ℱT cF))) := by
    rfl
  change ContinuousAt (fun t : {t : ℝ // 0 < t} =>
    realPartVectorL2 (ℱV.symm (stokesFourierMultiplier t.2 (ℱT cF))))
      ⟨t₀, ht₀⟩
  rw [hmapEq]
  exact hreal

end CKN.Leray

end
