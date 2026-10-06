/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatL4

/-!
# Norm bookkeeping for the forced heat response

Conversions between the real integrals used in the smooth-data estimates of
`lem:pv-stokes` and eLpNorm on the space-time slab `Q_τ`, and the
identification of the forced heat response of a smooth tensor with the
response vector of the energy estimates.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `L^r` norm of a nonnegative function whose `r`-th power is integrable. -/
theorem eLpNorm_eq_ofReal_integral_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} {r : ℝ} (hr : 0 < r) (hm : AEStronglyMeasurable h μ) (h0 : ∀ a, 0 ≤ h a)
    (hint : Integrable (fun a => h a ^ r) μ) :
    eLpNorm h (ENNReal.ofReal r) μ = ENNReal.ofReal ((∫ a, h a ^ r ∂μ) ^ (1 / r)) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hmem : MemLp h (ENNReal.ofReal r) μ := by
    rw [← integrable_norm_rpow_iff hm hr0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le]
    refine hint.congr (Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (h0 a)]
  rw [hmem.eLpNorm_eq_integral_rpow_norm hr0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, one_div]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with a
  simp only [Real.norm_eq_abs, abs_of_nonneg (h0 a)]

/-- The slab `Q_τ = ℝ³ × (0,τ)` carries the product of Lebesgue measure with
Lebesgue measure on `(0,τ]`. -/
theorem eLpNorm_spaceTimeSet_eq_window {E : Type*} [NormedAddCommGroup E]
    (f : ParabolicPoint → E) (p : ℝ≥0∞) (τ : ℝ) :
    eLpNorm f p (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) =
      eLpNorm (fun q : Vec3 × ℝ => f q) p
        ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) := by
  have hμ : ((volume : Measure Vec3).prod volume).restrict (univ ×ˢ Ioo 0 τ) =
      (volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  change eLpNorm (fun q : Vec3 × ℝ => f q) p
    (((volume : Measure Vec3).prod volume).restrict (univ ×ˢ Ioo 0 τ)) = _
  rw [hμ]

/-- A continuous compactly supported function has ofReal form for its `L^r`
norm. -/
theorem eLpNorm_eq_ofReal_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    {μ : Measure (Vec3 × ℝ)} [IsFiniteMeasureOnCompacts μ] {f : Vec3 × ℝ → E}
    (hf : Continuous f) (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q => ‖f q‖ ^ r) μ ∧
    eLpNorm f (ENNReal.ofReal r) μ = ENNReal.ofReal ((∫ q, ‖f q‖ ^ r ∂μ) ^ (1 / r)) := by
  have hint : Integrable (fun q => ‖f q‖ ^ r) μ :=
    (hf.norm.rpow_const fun _ => Or.inr hr.le).integrable_of_hasCompactSupport
      (hfc.norm.comp_left (g := fun y : ℝ => y ^ r) (Real.zero_rpow hr.ne'))
  refine ⟨hint, ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact eLpNorm_eq_ofReal_integral_rpow hr hf.norm.aestronglyMeasurable
    (fun q => norm_nonneg _) hint

/-- For a smooth compactly supported tensor, the forced heat response is the
response vector of the energy estimates. -/
theorem forcedHeat_eq_responseVec {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (z : ParabolicPoint) :
    forcedHeat G z = responseVec (fun i j (p : Vec3 × ℝ) => G i j p) z :=
  funext fun i => forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i z

/-- The spatial derivatives of the forced heat response of a smooth compactly
supported tensor are the response gradient of the energy estimates. -/
theorem spatialPartial_forcedHeat_eq {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (i j : Fin 3)
    (z : ParabolicPoint) :
    CKN.spatialPartial (fun w => forcedHeat G w i) j z =
      responseGrad (fun i j (p : Vec3 × ℝ) => G i j p) j z i := by
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv (vecTimeDiv g i)) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hG i) (vecTimeDiv_hasCompactSupport hGc i)
  have hfun : (fun w : ParabolicPoint => forcedHeat G w i) =
      (show ParabolicPoint → ℝ from causalHeatConv (vecTimeDiv g i)) :=
    funext fun w => forcedHeat_eq_causalHeatConv_vecTimeDiv hG hGc i w
  rw [hfun]
  exact spatialPartial_eq_fderiv_apply hhc j z.1 z.2

/-- The sup norm of a vector is at most the square root of its sum of squares. -/
theorem norm_le_sqrt_sum_sq (v : Vec3) : ‖v‖ ≤ (∑ i : Fin 3, v i ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← vec3EuclideanNorm]
  exact norm_le_vec3EuclideanNorm v

/-- The sum of squares of a `3 × 3` tensor is at most nine times its squared sup
norm. -/
theorem tensor_sum_sq_le (T : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, T i j ^ 2 ≤ 9 * ‖T‖ ^ 2 := by
  have hentry (i j : Fin 3) : T i j ^ 2 ≤ ‖T‖ ^ 2 := by
    have h1 : |T i j| ≤ ‖T‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (T i) j).trans (norm_le_pi_norm T i)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc
    ∑ i : Fin 3, ∑ j : Fin 3, T i j ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖T‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 9 * ‖T‖ ^ 2 := by simp; ring

end ESS

end
