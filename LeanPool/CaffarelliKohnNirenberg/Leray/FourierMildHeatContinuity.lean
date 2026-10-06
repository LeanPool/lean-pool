/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeat
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong continuity of the heat evolution

The Gaussian multiplier is strongly continuous on spatial `L²`, including at
initial time, as required by `lem:reg-local-mild`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The Fourier-side heat evolution obtained by multiplying a vector field by the heat symbol. -/
@[expose]
def heatSymbolField (t : ℝ) (F : ComplexVectorL2) :
    L2Vec3 → ComplexVec3 :=
  fun ξ => heatSymbol t ξ • F ξ

private theorem heatSymbolField_memLp (t : ℝ) (ht : 0 ≤ t)
    (F : ComplexVectorL2) : MemLp (heatSymbolField t F) 2 volume := by
  have hFmeas : AEStronglyMeasurable F volume := (Lp.memLp F).aestronglyMeasurable
  have hsymbol : Measurable (heatSymbol t) := by fun_prop [heatSymbol]
  have hmeas : AEStronglyMeasurable (heatSymbolField t F) volume := by
    exact (continuous_smul.comp_aestronglyMeasurable
      (hsymbol.aestronglyMeasurable.prodMk hFmeas)).congr
        (Filter.Eventually.of_forall fun _ => rfl)
  apply (Lp.memLp F).of_le_mul hmeas (c := 1)
  filter_upwards [] with ξ
  rw [heatSymbolField, norm_smul]
  exact mul_le_mul_of_nonneg_right (heatSymbol_norm_le_one ht ξ) (norm_nonneg _)

/-- The heat multiplier acting on a fixed frequency-space vector is strongly
continuous for nonnegative elapsed times. -/
theorem heatMultiplier_smul_continuousAt {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (F : ComplexVectorL2) :
    ContinuousAt
      (fun t : {t : ℝ // 0 ≤ t} => heatMultiplier t.1 t.2 • F)
      ⟨t₀, ht₀⟩ := by
  let q₀ : {t : ℝ // 0 ≤ t} := ⟨t₀, ht₀⟩
  let Φ : {t : ℝ // 0 ≤ t} → L2Vec3 → ComplexVec3 :=
    fun q => heatSymbolField q.1 F
  let f₀ : L2Vec3 → ComplexVec3 := Φ q₀
  have hMem (q : {t : ℝ // 0 ≤ t}) : MemLp (Φ q) 2 volume :=
    heatSymbolField_memLp q.1 q.2 F
  have hFpow : Integrable (fun ξ : L2Vec3 => ‖F ξ‖ ^ 2) volume :=
    (Lp.memLp F).integrable_norm_pow (by norm_num)
  have hIntegral : Tendsto
      (fun q : {t : ℝ // 0 ≤ t} =>
        ∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)
      (𝓝 q₀) (𝓝 0) := by
    let bound : L2Vec3 → ℝ := fun ξ => (2 * ‖F ξ‖) ^ 2
    have hboundInt : Integrable bound volume := by
      have hmul := hFpow.const_mul 4
      convert hmul using 1
      ext ξ
      ring
    have hDCT : Tendsto
        (fun q : {t : ℝ // 0 ≤ t} =>
          ∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)
        (𝓝 q₀) (𝓝 (∫ _ξ : L2Vec3, (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 q₀)
        (F := fun q ξ => ‖Φ q ξ - f₀ ξ‖ ^ 2)
        (f := fun _ : L2Vec3 => (0 : ℝ)) bound ?_ ?_ hboundInt ?_
      · filter_upwards [] with q
        exact (continuous_norm.pow 2).comp_aestronglyMeasurable
          ((hMem q).sub (by simpa [f₀] using hMem q₀)).aestronglyMeasurable
      · filter_upwards [] with q
        filter_upwards [] with ξ
        have hFbound (r : {t : ℝ // 0 ≤ t}) : ‖Φ r ξ‖ ≤ ‖F ξ‖ := by
          change ‖heatSymbol r.1 ξ • F ξ‖ ≤ ‖F ξ‖
          rw [norm_smul]
          calc
            ‖heatSymbol r.1 ξ‖ * ‖F ξ‖ ≤ 1 * ‖F ξ‖ :=
              mul_le_mul_of_nonneg_right (heatSymbol_norm_le_one r.2 ξ)
                (norm_nonneg _)
            _ = ‖F ξ‖ := by simp
        have hq : ‖Φ q ξ‖ ≤ ‖F ξ‖ := hFbound q
        have h₀ : ‖f₀ ξ‖ ≤ ‖F ξ‖ := by simpa [f₀] using hFbound q₀
        have hnorm : ‖Φ q ξ - f₀ ξ‖ ≤ 2 * ‖F ξ‖ := by
          calc
            ‖Φ q ξ - f₀ ξ‖ ≤ ‖Φ q ξ‖ + ‖f₀ ξ‖ := norm_sub_le _ _
            _ ≤ ‖F ξ‖ + ‖F ξ‖ := add_le_add hq h₀
            _ = 2 * ‖F ξ‖ := by ring
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
        have hsqNonneg : 0 ≤ (‖Φ q ξ - f₀ ξ‖ : ℝ) ^ 2 := sq_nonneg _
        simpa [Real.norm_eq_abs, abs_of_nonneg hsqNonneg, bound] using hsq
      · filter_upwards [] with ξ
        have hformula : Tendsto (fun q : {t : ℝ // 0 ≤ t} => Φ q ξ)
            (𝓝 q₀) (𝓝 (f₀ ξ)) := by
          have hcont : Continuous (fun t : ℝ => heatSymbol t ξ • F ξ) := by
            fun_prop [heatSymbol]
          simpa [Φ, f₀, heatSymbolField, q₀, Function.comp_def] using
            hcont.continuousAt.tendsto.comp
              continuous_subtype_val.continuousAt.tendsto
        have hdiff : Tendsto (fun q : {t : ℝ // 0 ≤ t} => Φ q ξ - f₀ ξ)
            (𝓝 q₀) (𝓝 0) := by
          have hconst : Tendsto (fun _ : {t : ℝ // 0 ≤ t} => f₀ ξ)
              (𝓝 q₀) (𝓝 (f₀ ξ)) := tendsto_const_nhds
          simpa [Φ] using hformula.sub hconst
        have hnorm := continuous_norm.continuousAt.tendsto.comp hdiff
        have hpow := (continuousAt_id.pow 2).tendsto.comp hnorm
        simpa [Φ, f₀, q₀, sub_self, Function.comp_def] using hpow
    simpa [integral_zero] using hDCT
  have hLpTendsto : Tendsto
      (fun q : {t : ℝ // 0 ≤ t} => (hMem q).toLp (Φ q))
      (𝓝 q₀) (𝓝 ((hMem q₀).toLp f₀)) := by
    have hroot : Tendsto
        (fun q : {t : ℝ // 0 ≤ t} =>
          Real.sqrt (∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2))
        (𝓝 q₀) (𝓝 0) := by
      simpa [Function.comp_def] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hIntegral)
    have hnorm : Tendsto
        (fun q : {t : ℝ // 0 ≤ t} => eLpNorm (Φ q - f₀) 2 volume)
        (𝓝 q₀) (𝓝 0) := by
      have hformulaNorm (q : {t : ℝ // 0 ≤ t}) :
          eLpNorm (Φ q - f₀) 2 volume =
            ENNReal.ofReal
              (Real.sqrt (∫ ξ : L2Vec3, ‖Φ q ξ - f₀ ξ‖ ^ 2)) := by
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
  have hformulaToLp (q : {t : ℝ // 0 ≤ t}) :
      (hMem q).toLp (Φ q) = heatMultiplier q.1 q.2 • F := by
    let hHeatMem : MemLp (heatSymbol q.1) ∞ volume := by
      apply memLp_top_of_bound
      · fun_prop [heatSymbol]
      · filter_upwards [] with ξ
        exact heatSymbol_norm_le_one q.2 ξ
    have hmul : heatMultiplier q.1 q.2 =ᵐ[volume] heatSymbol q.1 := by
      filter_upwards [hHeatMem.coeFn_toLp] with ξ hξ
      change hHeatMem.toLp (heatSymbol q.1) ξ = heatSymbol q.1 ξ at hξ
      simpa [heatMultiplier, hHeatMem] using hξ
    have hsmul : (fun ξ : L2Vec3 => (heatMultiplier q.1 q.2 • F) ξ) =ᵐ[volume]
        fun ξ => heatMultiplier q.1 q.2 ξ • F ξ :=
      Lp.coeFn_lpSMul (heatMultiplier q.1 q.2) F
    apply Lp.ext
    filter_upwards [(hMem q).coeFn_toLp, hmul, hsmul] with ξ hto hmul hs
    calc
      (hMem q).toLp (Φ q) ξ = Φ q ξ := hto
      _ = heatSymbol q.1 ξ • F ξ := by rfl
      _ = heatMultiplier q.1 q.2 ξ • F ξ := by rw [hmul.symm]
      _ = (heatMultiplier q.1 q.2 • F) ξ := hs.symm
  have hLpTendsto' : Tendsto
      (fun q : {t : ℝ // 0 ≤ t} => heatMultiplier q.1 q.2 • F)
      (𝓝 q₀) (𝓝 (heatMultiplier t₀ ht₀ • F)) := by
    have hEnd : (hMem q₀).toLp (Φ q₀) = heatMultiplier t₀ ht₀ • F := by
      simpa [q₀] using hformulaToLp q₀
    have hEq : (fun q : {t : ℝ // 0 ≤ t} => (hMem q).toLp (Φ q)) =
        fun q => heatMultiplier q.1 q.2 • F := by
      funext q
      exact hformulaToLp q
    rw [← hEq, ← hEnd]
    exact hLpTendsto
  exact hLpTendsto'

/-- The complex heat semigroup is strongly continuous, including at time zero. -/
theorem heatSemigroup_continuousAt {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (F : ComplexVectorL2) :
    ContinuousAt
      (fun t : {t : ℝ // 0 ≤ t} => heatSemigroup t.1 t.2 F)
      ⟨t₀, ht₀⟩ := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have hmult := heatMultiplier_smul_continuousAt ht₀ (ℱ F)
  change ContinuousAt
    (fun t : {t : ℝ // 0 ≤ t} => ℱ.symm (heatMultiplier t.1 t.2 • ℱ F))
    ⟨t₀, ht₀⟩
  exact ℱ.symm.continuous.continuousAt.comp hmult

/-- The real heat evolution is strongly continuous at every nonnegative time,
including the initial state required by `lem:reg-local-mild`. -/
theorem realHeatOperator_continuousAt {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (f : RealVectorL2) :
    ContinuousAt
      (fun t : {t : ℝ // 0 ≤ t} => realHeatOperator t.1 t.2 f)
      ⟨t₀, ht₀⟩ := by
  have hcomplex := heatSemigroup_continuousAt ht₀ (complexifyVectorL2 f)
  have hreal : ContinuousAt
      (fun t : {t : ℝ // 0 ≤ t} =>
        realPartVectorL2 (heatSemigroup t.1 t.2 (complexifyVectorL2 f)))
      ⟨t₀, ht₀⟩ :=
    realPartVectorL2.continuous.continuousAt.comp hcomplex
  simpa [realHeatOperator] using hreal

end CKN.Leray

end
