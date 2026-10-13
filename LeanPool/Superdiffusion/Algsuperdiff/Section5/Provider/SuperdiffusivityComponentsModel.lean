/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Carrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SuperdiffusivityAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationAtRandomScale

/-!
# SuperdiffusivityComponentsModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Model data for the annealed superdiffusivity components

This module supplies the six non-quenched fields of
`SuperdiffusivityV2Components` from the scale family and the
generator-renormalization family.  The selected random variables are exactly

```text
  EB (confinementScale S L omega) omega,
  3 ^ confinementScale S L omega,
```

where `L = K sqrt(|log gamma|) intrinsicScale`.  The final constructor keeps
the two quenched inequalities as separately named inputs; they are the outputs
of `QuenchedMomentsComposer.lean`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The common constant envelope -/

/-- A common constant for the selected renormalization-error moments, the
selected confinement-radius moment, and the loss in the admissible exponent
range. -/
def superdiffusivityV2ComponentConstant (CS Cren K : ℝ) : ℝ :=
  max 1 (max (8 * Cren)
    (max (81 * Real.sqrt 2 * CS * Cren) (2187 / 2 * CS ^ (2 : ℕ) * K)))

theorem eight_mul_le_superdiffusivityV2ComponentConstant (CS Cren K : ℝ) :
    8 * Cren ≤ superdiffusivityV2ComponentConstant CS Cren K :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem errorCoefficient_le_superdiffusivityV2ComponentConstant (CS Cren K : ℝ) :
    81 * Real.sqrt 2 * CS * Cren ≤
      superdiffusivityV2ComponentConstant CS Cren K :=
  calc
    81 * Real.sqrt 2 * CS * Cren ≤
        max (81 * Real.sqrt 2 * CS * Cren) (2187 / 2 * CS ^ (2 : ℕ) * K) :=
      le_max_left _ _
    _ ≤ max (8 * Cren)
        (max (81 * Real.sqrt 2 * CS * Cren) (2187 / 2 * CS ^ (2 : ℕ) * K)) :=
      le_max_right _ _
    _ ≤ superdiffusivityV2ComponentConstant CS Cren K := le_max_right _ _

theorem radiusCoefficient_le_superdiffusivityV2ComponentConstant (CS Cren K : ℝ) :
    2187 / 2 * CS ^ (2 : ℕ) * K ≤
      superdiffusivityV2ComponentConstant CS Cren K :=
  calc
    2187 / 2 * CS ^ (2 : ℕ) * K ≤
        max (81 * Real.sqrt 2 * CS * Cren) (2187 / 2 * CS ^ (2 : ℕ) * K) :=
      le_max_right _ _
    _ ≤ max (8 * Cren)
        (max (81 * Real.sqrt 2 * CS * Cren) (2187 / 2 * CS ^ (2 : ℕ) * K)) :=
      le_max_right _ _
    _ ≤ superdiffusivityV2ComponentConstant CS Cren K := le_max_right _ _

/-! ## Measurability and transport to the full-sample carrier -/

private theorem measurable_intFamily_apply {Omega : Type*} [MeasurableSpace Omega]
    {F : ℤ → Omega → ℝ} (hF : ∀ n, Measurable (F n)) {m : Omega → ℤ}
    (hm : Measurable m) : Measurable fun omega => F (m omega) omega := by
  let sets : ℤ → Set Omega := fun n => {omega | m omega = n}
  have hsets : ∀ n, MeasurableSet (sets n) := fun n =>
    measurableSet_eq_fun hm measurable_const
  obtain ⟨f, hf, hfon⟩ := exists_measurable_piecewise sets hsets F hF (by
    intro i j hij omega homega
    exact (hij (homega.1.symm.trans homega.2)).elim)
  have hEq : f = fun omega => F (m omega) omega := by
    funext omega
    exact hfon (m omega) (by simp only [sets, Set.mem_ofPred_eq])
  rw [← hEq]
  exact hf

private theorem lintegral_fullSample_comp_val (M : ABKModel d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ omega : FullSample d M.gamma, f omega.1 ∂(fullSampleLaw M).toMeasure) =
      ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  calc
    (∫⁻ omega : FullSample d M.gamma, f omega.1 ∂(fullSampleLaw M).toMeasure) =
        ∫⁻ omega, f omega
          ∂Measure.map (Subtype.val : FullSample d M.gamma → Cutoff.CutoffSample d)
            (fullSampleLaw M).toMeasure :=
      (lintegral_map hf measurable_subtype_coe).symm
    _ = ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      rw [map_fullSampleLaw_val M]

/-! ## Positivity and measurability -/

/-- The selected renormalization error is nonnegative on the full-sample
carrier. -/
theorem selectedRenormalizationError_nonneg (M : ABKModel d)
    (S EB : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ)
    (hEBnn : ∀ n omega, 0 ≤ EB n omega) :
    ∀ omega : FullSample d M.gamma,
      0 ≤ EB (confinementScale S L omega.1) omega.1 :=
  fun omega => hEBnn (confinementScale S L omega.1) omega.1

/-- The selected triadic confinement radius is nonnegative. -/
theorem selectedConfinementRadius_nonneg (M : ABKModel d)
    (S : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ) :
    ∀ omega : FullSample d M.gamma,
      0 ≤ (3 : ℝ) ^ (confinementScale S L omega.1) :=
  fun omega => (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le

/-- The selected renormalization error is almost everywhere measurable on the
full-sample carrier. -/
theorem selectedRenormalizationError_aemeasurable (M : ABKModel d)
    (S EB : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ)
    (hSmeas : ∀ n, Measurable (S n)) (hEBmeas : ∀ n, Measurable (EB n)) :
    AEMeasurable (fun omega : FullSample d M.gamma =>
      EB (confinementScale S L omega.1) omega.1) (fullSampleLaw M).toMeasure := by
  have hm : Measurable fun omega : Cutoff.CutoffSample d => confinementScale S L omega :=
    measurable_confinementScale hSmeas L
  exact (measurable_intFamily_apply hEBmeas hm).comp measurable_subtype_coe |>.aemeasurable

/-- The selected triadic confinement radius is almost everywhere measurable
on the full-sample carrier. -/
theorem selectedConfinementRadius_aemeasurable (M : ABKModel d)
    (S : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ)
    (hSmeas : ∀ n, Measurable (S n)) :
    AEMeasurable (fun omega : FullSample d M.gamma =>
      (3 : ℝ) ^ (confinementScale S L omega.1)) (fullSampleLaw M).toMeasure := by
  have hm : Measurable fun omega : Cutoff.CutoffSample d => confinementScale S L omega :=
    measurable_confinementScale hSmeas L
  exact ((measurable_of_countable fun n : ℤ => (3 : ℝ) ^ n).comp hm).comp
    measurable_subtype_coe |>.aemeasurable

/-! ## Exponent and amplitude arithmetic -/

private theorem eight_mul_le_renormalization_range {p C0 Cren gamma logWeight : ℝ}
    (hCren : 0 < Cren) (hgamma : 0 < gamma)
    (hlog : 1 ≤ logWeight) (hC0 : 8 * Cren ≤ C0)
    (hrange : p ≤ C0⁻¹ * gamma⁻¹ * logWeight ^ (-6 : ℤ)) :
    8 * p ≤ Cren⁻¹ * gamma⁻¹ * logWeight⁻¹ := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le (mul_pos (by norm_num) hCren) hC0
  have hcoeff : 8 * C0⁻¹ ≤ Cren⁻¹ := by
    have hbase : C0⁻¹ ≤ (8 * Cren)⁻¹ :=
      (inv_le_inv₀ hC0pos (mul_pos (by norm_num) hCren)).2 hC0
    calc
      8 * C0⁻¹ ≤ 8 * (8 * Cren)⁻¹ :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = Cren⁻¹ := by field_simp
  have hlogpos : 0 < logWeight := zero_lt_one.trans_le hlog
  have hlogpow : logWeight ≤ logWeight ^ (6 : ℕ) := by
    calc
      logWeight = logWeight * 1 := (mul_one _).symm
      _ ≤ logWeight * logWeight ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlog) hlogpos.le
      _ = logWeight ^ (6 : ℕ) := by ring
  have hlogInv : logWeight ^ (-6 : ℤ) ≤ logWeight⁻¹ := by
    rw [zpow_neg]
    exact (inv_le_inv₀ (pow_pos hlogpos 6) hlogpos).2 hlogpow
  have hgammaInv : 0 ≤ gamma⁻¹ := inv_nonneg.mpr hgamma.le
  have hlogNeg : 0 ≤ logWeight ^ (-6 : ℤ) := zpow_nonneg hlogpos.le _
  calc
    8 * p ≤ 8 * (C0⁻¹ * gamma⁻¹ * logWeight ^ (-6 : ℤ)) :=
      mul_le_mul_of_nonneg_left hrange (by norm_num)
    _ = (8 * C0⁻¹) * gamma⁻¹ * logWeight ^ (-6 : ℤ) := by ring
    _ ≤ Cren⁻¹ * gamma⁻¹ * logWeight ^ (-6 : ℤ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff hgammaInv) hlogNeg
    _ ≤ Cren⁻¹ * gamma⁻¹ * logWeight⁻¹ := by
      exact mul_le_mul_of_nonneg_left hlogInv
        (mul_nonneg (inv_nonneg.mpr hCren.le) hgammaInv)

private theorem sqrt_two_mul_add_le_two_mul_add {p L : ℝ} :
    Real.sqrt (2 * p) + Real.sqrt L ≤ 2 * (Real.sqrt p + Real.sqrt L) := by
  have hsqrt : Real.sqrt (2 * p) = Real.sqrt 2 * Real.sqrt p :=
    Real.sqrt_mul (by norm_num) p
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  rw [hsqrt]
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg p))
    (le_mul_of_one_le_left (Real.sqrt_nonneg L) (by norm_num : (1 : ℝ) ≤ 2))

private theorem sqrt_four_mul_add_le_two_mul_add {p L : ℝ} :
    Real.sqrt (4 * p) + Real.sqrt L ≤ 2 * (Real.sqrt p + Real.sqrt L) := by
  have hsqrt : Real.sqrt (4 * p) = 2 * Real.sqrt p := by
    calc
      Real.sqrt (4 * p) = Real.sqrt 4 * Real.sqrt p := Real.sqrt_mul (by norm_num) p
      _ = 2 * Real.sqrt p := by norm_num
  rw [hsqrt]
  rw [mul_add]
  exact add_le_add le_rfl
    (le_mul_of_one_le_left (Real.sqrt_nonneg L) (by norm_num : (1 : ℝ) ≤ 2))

/-! ## The selected moments on the full-sample carrier -/

/-- The `2p` moment of the selected renormalization error, in exactly the
proposition used by `SuperdiffusivityV2Components`. -/
theorem selectedRenormalizationError_moment_two (M : ABKModel d)
    [NeZero d]
    {cstar t p C0 CS Cren K : ℝ} (hcstar : 0 < cstar) (ht : 0 < t)
    (hp : 1 ≤ p) (hCS : 1 ≤ CS) (hCren : 0 < Cren) (hK : 1 ≤ K)
    (hC0 : superdiffusivityV2ComponentConstant CS Cren K ≤ C0)
    (hrange : p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
    {S EB : ℤ → Cutoff.CutoffSample d → ℝ}
    (hSmeas : ∀ n, Measurable (S n)) (hSnn : ∀ n omega, 0 ≤ S n omega)
    (hSmom4 : ∀ n : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p))
    (hEBmeas : ∀ n, Measurable (EB n))
    (hEBmom : ∀ n : ℤ, ∀ q : ℝ, 1 ≤ q →
      q ≤ Cren⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (Cren * (Real.sqrt q + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ q) :
    (∫⁻ omega : FullSample d M.gamma,
        ENNReal.ofReal (EB (confinementScale S
          (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
          omega.1) omega.1) ^ (2 * p) ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ (2 * p) := by
  let L := K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t
  have hlog := one_le_abs_log M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter
  have hL : 0 < L := by
    dsimp only [L]
    have hK0 : 0 < K := zero_lt_one.trans_le hK
    have hsqrtLog : 0 < Real.sqrt |Real.log M.gamma| :=
      zero_lt_one.trans_le (one_le_sqrt_abs_log M.shellPrefix.gamma_pos
        M.shellPrefix.gamma_le_quarter)
    exact mul_pos (mul_pos hK0 hsqrtLog)
      (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht)
  have hrange8 := eight_mul_le_renormalization_range hCren
    M.shellPrefix.gamma_pos hlog
    ((eight_mul_le_superdiffusivityV2ComponentConstant CS Cren K).trans hC0) hrange
  have hrange4 : 2 * (2 * p) ≤
      Cren⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
    have hp0 : 0 ≤ p := zero_le_one.trans hp
    linarith only [hrange8, hp0]
  have hraw := lintegral_renormalizationError_selectedConfinementScale_le
    (S := S) (EB := EB) (CS := CS) (p := 2 * p) (C := Cren) M hSmeas hSnn hL
    hCS (by linarith only [hp]) (by
      simpa only [show 2 * (2 * p) = 4 * p by ring] using hSmom4)
    hEBmeas hCren hrange4 hEBmom
  have hselected : Measurable fun omega : Cutoff.CutoffSample d =>
      EB (confinementScale S L omega) omega :=
    measurable_intFamily_apply hEBmeas (measurable_confinementScale hSmeas L)
  have htransport :
      (∫⁻ omega : FullSample d M.gamma,
          ENNReal.ofReal (EB (confinementScale S L omega.1) omega.1) ^ (2 * p)
            ∂(fullSampleLaw M).toMeasure) =
        ∫⁻ omega, ENNReal.ofReal (EB (confinementScale S L omega) omega) ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    exact lintegral_fullSample_comp_val M
      ((ENNReal.measurable_ofReal.comp hselected).pow_const (2 * p))
  rw [htransport]
  refine hraw.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_)
    (mul_nonneg (by norm_num) (zero_le_one.trans hp)))
  have hsqrt := sqrt_two_mul_add_le_two_mul_add (p := p) (L := |Real.log M.gamma|)
  have hcoeff :=
    (errorCoefficient_le_superdiffusivityV2ComponentConstant CS Cren K).trans hC0
  have htail : 0 ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
      (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by positivity
  calc
    81 / 2 * Real.sqrt 2 * CS * Cren *
          (Real.sqrt (2 * p) + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) ≤
        81 / 2 * Real.sqrt 2 * CS * Cren *
          (2 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|)) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by
      gcongr
    _ = (81 * Real.sqrt 2 * CS * Cren) *
          ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ))) := by ring
    _ ≤ C0 * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ))) :=
      mul_le_mul_of_nonneg_right hcoeff htail
    _ = C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by ring

/-- The `4p` moment of the selected renormalization error, in exactly the
proposition used by `SuperdiffusivityV2Components`. -/
theorem selectedRenormalizationError_moment_four (M : ABKModel d)
    [NeZero d]
    {cstar t p C0 CS Cren K : ℝ} (hcstar : 0 < cstar) (ht : 0 < t)
    (hp : 1 ≤ p) (hCS : 1 ≤ CS) (hCren : 0 < Cren) (hK : 1 ≤ K)
    (hC0 : superdiffusivityV2ComponentConstant CS Cren K ≤ C0)
    (hrange : p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
    {S EB : ℤ → Cutoff.CutoffSample d → ℝ}
    (hSmeas : ∀ n, Measurable (S n)) (hSnn : ∀ n omega, 0 ≤ S n omega)
    (hSmom8 : ∀ n : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p))
    (hEBmeas : ∀ n, Measurable (EB n))
    (hEBmom : ∀ n : ℤ, ∀ q : ℝ, 1 ≤ q →
      q ≤ Cren⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (Cren * (Real.sqrt q + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ q) :
    (∫⁻ omega : FullSample d M.gamma,
        ENNReal.ofReal (EB (confinementScale S
          (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
          omega.1) omega.1) ^ (4 * p) ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ (4 * p) := by
  let L := K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t
  have hlog := one_le_abs_log M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter
  have hL : 0 < L := by
    dsimp only [L]
    have hK0 : 0 < K := zero_lt_one.trans_le hK
    have hsqrtLog : 0 < Real.sqrt |Real.log M.gamma| :=
      zero_lt_one.trans_le (one_le_sqrt_abs_log M.shellPrefix.gamma_pos
        M.shellPrefix.gamma_le_quarter)
    exact mul_pos (mul_pos hK0 hsqrtLog)
      (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht)
  have hrange8 := eight_mul_le_renormalization_range hCren
    M.shellPrefix.gamma_pos hlog
    ((eight_mul_le_superdiffusivityV2ComponentConstant CS Cren K).trans hC0) hrange
  have hraw := lintegral_renormalizationError_selectedConfinementScale_le
    (S := S) (EB := EB) (CS := CS) (p := 4 * p) (C := Cren) M hSmeas hSnn hL
    hCS (by linarith only [hp]) (by
      simpa only [show 2 * (4 * p) = 8 * p by ring] using hSmom8)
    hEBmeas hCren (by simpa only [show 2 * (4 * p) = 8 * p by ring] using hrange8) hEBmom
  have hselected : Measurable fun omega : Cutoff.CutoffSample d =>
      EB (confinementScale S L omega) omega :=
    measurable_intFamily_apply hEBmeas (measurable_confinementScale hSmeas L)
  have htransport :
      (∫⁻ omega : FullSample d M.gamma,
          ENNReal.ofReal (EB (confinementScale S L omega.1) omega.1) ^ (4 * p)
            ∂(fullSampleLaw M).toMeasure) =
        ∫⁻ omega, ENNReal.ofReal (EB (confinementScale S L omega) omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    exact lintegral_fullSample_comp_val M
      ((ENNReal.measurable_ofReal.comp hselected).pow_const (4 * p))
  rw [htransport]
  refine hraw.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_)
    (mul_nonneg (by norm_num) (zero_le_one.trans hp)))
  have hsqrt := sqrt_four_mul_add_le_two_mul_add (p := p) (L := |Real.log M.gamma|)
  have hcoeff :=
    (errorCoefficient_le_superdiffusivityV2ComponentConstant CS Cren K).trans hC0
  have htail : 0 ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
      (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by positivity
  calc
    81 / 2 * Real.sqrt 2 * CS * Cren *
          (Real.sqrt (4 * p) + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) ≤
        81 / 2 * Real.sqrt 2 * CS * Cren *
          (2 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|)) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by
      gcongr
    _ = (81 * Real.sqrt 2 * CS * Cren) *
          ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ))) := by ring
    _ ≤ C0 * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ))) :=
      mul_le_mul_of_nonneg_right hcoeff htail
    _ = C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by ring

/-- The `4p` moment of the selected triadic confinement radius, in exactly the
proposition used by `SuperdiffusivityV2Components`. -/
theorem selectedConfinementRadius_moment_four (M : ABKModel d)
    [NeZero d]
    {cstar t p C0 CS K Cren : ℝ} (hcstar : 0 < cstar) (ht : 0 < t)
    (hp : 1 ≤ p) (hCS : 1 ≤ CS) (hK : 1 ≤ K)
    (hC0 : superdiffusivityV2ComponentConstant CS Cren K ≤ C0)
    {S : ℤ → Cutoff.CutoffSample d → ℝ}
    (hSmeas : ∀ n, Measurable (S n)) (hSnn : ∀ n omega, 0 ≤ S n omega)
    (hSmom8 : ∀ n : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p)) :
    (∫⁻ omega : FullSample d M.gamma,
        ENNReal.ofReal ((3 : ℝ) ^ (confinementScale S
          (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
          omega.1)) ^ (4 * p) ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * Real.sqrt |Real.log M.gamma| *
        intrinsicScale M.nu cstar M.gamma t) ^ (4 * p) := by
  let L := K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t
  have hraw := lintegral_three_zpow_selectedConfinementScale_le
    (S := S) (p := 4 * p) (C := CS) (Cutoff.cutoffSampleLaw M).toMeasure
    hSmeas hSnn M.nu_pos hcstar
    M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter ht hK hCS
    (by linarith only [hp]) (by
      simpa only [show 2 * (4 * p) = 8 * p by ring] using hSmom8)
  have hradius : Measurable fun omega : Cutoff.CutoffSample d =>
      (3 : ℝ) ^ confinementScale S L omega :=
    (measurable_of_countable fun n : ℤ => (3 : ℝ) ^ n).comp
      (measurable_confinementScale hSmeas L)
  have htransport :
      (∫⁻ omega : FullSample d M.gamma,
          ENNReal.ofReal ((3 : ℝ) ^ confinementScale S L omega.1) ^ (4 * p)
            ∂(fullSampleLaw M).toMeasure) =
        ∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ confinementScale S L omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    exact lintegral_fullSample_comp_val M
      ((ENNReal.measurable_ofReal.comp hradius).pow_const (4 * p))
  rw [htransport]
  refine hraw.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_)
    (mul_nonneg (by norm_num) (zero_le_one.trans hp)))
  have hcoeff :=
    (radiusCoefficient_le_superdiffusivityV2ComponentConstant CS Cren K).trans hC0
  have htail : 0 ≤ Real.sqrt |Real.log M.gamma| *
      intrinsicScale M.nu cstar M.gamma t :=
    mul_nonneg (Real.sqrt_nonneg _)
      (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht).le
  calc
    2187 / 2 * CS ^ (2 : ℕ) * K * Real.sqrt |Real.log M.gamma| *
          intrinsicScale M.nu cstar M.gamma t =
        (2187 / 2 * CS ^ (2 : ℕ) * K) *
          (Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t) := by ring
    _ ≤ C0 * (Real.sqrt |Real.log M.gamma| *
          intrinsicScale M.nu cstar M.gamma t) :=
      mul_le_mul_of_nonneg_right hcoeff htail
    _ = C0 * Real.sqrt |Real.log M.gamma| *
          intrinsicScale M.nu cstar M.gamma t := by ring

/-! ## Construction once the two quenched fields are supplied -/

/-- Build the full component structure from the scale and renormalization
families once the two quenched inequalities have been supplied by the quenched
composer. -/
def superdiffusivityV2Components_of_quenched (M : ABKModel d)
    [NeZero d]
    {cstar t p C0 CS Cren K : ℝ} (hcstar : 0 < cstar) (ht : 0 < t)
    (hp : 1 ≤ p) (hCS : 1 ≤ CS) (hCren : 0 < Cren) (hK : 1 ≤ K)
    (hC0 : superdiffusivityV2ComponentConstant CS Cren K ≤ C0)
    (hrange : p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
    {S EB : ℤ → Cutoff.CutoffSample d → ℝ}
    (hSmeas : ∀ n, Measurable (S n)) (hSnn : ∀ n omega, 0 ≤ S n omega)
    (hSmom4 : ∀ n : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (4 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (4 * p))
    (hSmom8 : ∀ n : ℤ,
      (∫⁻ omega, ENNReal.ofReal (S n omega) ^ (8 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal CS ^ (8 * p))
    (hEBnn : ∀ n omega, 0 ≤ EB n omega) (hEBmeas : ∀ n, Measurable (EB n))
    (hEBmom : ∀ n : ℤ, ∀ q : ℝ, 1 ≤ q →
      q ≤ Cren⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ENNReal.ofReal (EB n omega) ^ q
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (Cren * (Real.sqrt q + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ q)
    (hsecond : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
       letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
       |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
            ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) -
          2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2|) ≤
        C0 * (EB (confinementScale S
          (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
          omega.1) omega.1 + Real.sqrt M.gamma * |Real.log M.gamma|) *
          ((3 : ℝ) ^ confinementScale S
            (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
            omega.1) ^ 2)
    (hmeanSq : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
      (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
       letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
       vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
            ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d))))) ≤
        C0 * (EB (confinementScale S
          (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
          omega.1) omega.1 ^ 2 + M.gamma ^ (80 : ℕ)) *
          ((3 : ℝ) ^ confinementScale S
            (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
            omega.1) ^ 2) :
    SuperdiffusivityV2Components M cstar t p C0 := by
  refine
    { renormalizationError := fun omega => EB (confinementScale S
        (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t)
        omega.1) omega.1
      confinementRadius := fun omega => (3 : ℝ) ^ confinementScale S
        (K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t) omega.1
      renormalizationError_nonneg := selectedRenormalizationError_nonneg M S EB _ hEBnn
      confinementRadius_nonneg := selectedConfinementRadius_nonneg M S _
      renormalizationError_aemeasurable :=
        selectedRenormalizationError_aemeasurable M S EB _ hSmeas hEBmeas
      confinementRadius_aemeasurable :=
        selectedConfinementRadius_aemeasurable M S _ hSmeas
      secondMoment_quenched := hsecond
      meanSq_quenched := hmeanSq
      renormalizationError_moment_two :=
        selectedRenormalizationError_moment_two M hcstar ht hp hCS hCren hK hC0 hrange
          hSmeas hSnn hSmom4 hEBmeas hEBmom
      renormalizationError_moment_four :=
        selectedRenormalizationError_moment_four M hcstar ht hp hCS hCren hK hC0 hrange
          hSmeas hSnn hSmom8 hEBmeas hEBmom
      confinementRadius_moment_four :=
        selectedConfinementRadius_moment_four M hcstar ht hp hCS hK hC0 hSmeas hSnn
          hSmom8 }

end

end Algsuperdiff.Section5.Provider
