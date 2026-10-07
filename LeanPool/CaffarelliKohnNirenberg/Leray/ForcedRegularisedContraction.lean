/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedForceDuhamel
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTruncation
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalEstimates
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The truncated forced mild map on a bounded interval

The right-hand side of `eq:reg-mild-forced`, with the regularized tensor of
the radially truncated velocity, defines a map on continuous `L²` curves over
`[0, T]`. The Abel kernel paired with an exponential weight has integral of
order `λ^{-1/2}`, which makes the map a contraction in an exponentially
weighted norm; this gives existence and uniqueness of the truncated solution
on the whole interval, as in `lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- The weighted Abel kernel has integral at most `λ^{-1/2} Γ(1/2)`. -/
theorem integral_abelKernel_exp_le {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    ∫ s in Ioc 0 t, (t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * (t - s)) ≤
      lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2 : ℝ)) (p := 1) (b := lam)
    (by norm_num) one_pos hlam
  have hval := integral_rpow_mul_exp_neg_mul_rpow (q := -(1 / 2 : ℝ)) (p := 1) (b := lam)
    one_pos (by norm_num) hlam
  simp only [Real.rpow_one, div_one, mul_one] at hint hval
  rw [← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left
      (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)) t]
  simp only [sub_self, sub_zero]
  rw [intervalIntegral.integral_of_le ht]
  have hmono : ∫ τ in Ioc 0 t, τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) ≤
      ∫ τ in Ioi 0, τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hτ) _) (Real.exp_pos _).le
  refine hmono.trans_eq ?_
  rw [hval]
  norm_num

theorem continuous_forcedTruncTensor (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (hR : 0 ≤ R) : Continuous (forcedTruncTensor ρ ε hε R) := by
  have hK := (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨4 * regularizedMildMollifierConstant ρ ε * R,
    by positivity⟩) fun v w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_forcedTruncTensor_sub_le ρ ε hε hR v w

/-- The truncated tensor curve of a trajectory on `[0, T]`, clamped to all real
times. -/
@[expose]
def forcedTensorCurve (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (R T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2)) : ℝ → RealTensorL2 :=
  fun s => forcedTruncTensor ρ ε hε R (u (regularizedMildTimeClamp T hT s))

theorem continuous_forcedTensorCurve (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (hR : 0 ≤ R) (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    Continuous (forcedTensorCurve ρ ε hε R T hT u) :=
  (continuous_forcedTruncTensor ρ ε hε hR).comp
    (u.continuous.comp (regularizedMildTimeClamp_continuous T hT))

theorem norm_forcedTensorCurve_le (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {R : ℝ}
    (hR : 0 ≤ R) (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (s : ℝ) :
    ‖forcedTensorCurve ρ ε hε R T hT u s‖ ≤ regularizedMildMollifierConstant ρ ε * R ^ 2 :=
  norm_forcedTruncTensor_le ρ ε hε hR _

/-- The truncated forced mild map on continuous curves over `[0, T]`. -/
@[expose]
def forcedMildMap (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    C(RegularizedMildTimeInterval T, RealVectorL2) := by
  let F := forcedTensorCurve ρ ε hε R T hT u
  let C := regularizedMildMollifierConstant ρ ε * R ^ 2
  have hFcont : Continuous F := continuous_forcedTensorCurve ρ ε hε hR T hT u
  have hFC : ∀ s, ‖F s‖ ≤ C := norm_forcedTensorCurve_le ρ ε hε hR T hT u
  have hC : 0 ≤ C :=
    mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε) (sq_nonneg R)
  let nonnegativeTime : RegularizedMildTimeInterval T → {s : ℝ // 0 ≤ s} :=
    fun t => ⟨t, t.2.1⟩
  have hnonnegativeTime : Continuous nonnegativeTime :=
    continuous_subtype_val.subtype_mk fun t => t.2.1
  have hheat : Continuous
      (fun t : RegularizedMildTimeInterval T => realHeatOperator t.1 t.2.1 b) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hAt := (realHeatOperator_continuousAt t.2.1 b).comp hnonnegativeTime.continuousAt
    change ContinuousAt
      (fun q => realHeatOperator (nonnegativeTime q).1 (nonnegativeTime q).2 b) t
    exact hAt
  have hstokes : Continuous (fun t : RegularizedMildTimeInterval T =>
      regularizedMildStokesIntegral F t.1) := by
    have heq : (fun t : RegularizedMildTimeInterval T => regularizedMildStokesIntegral F t.1) =
        fun t => ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ := by
      funext t
      exact regularizedMildStokesIntegral_eq_shifted T t.1 hT t.2.1 t.2.2 hFcont C hFC hC
    rw [heq]
    exact (mildShiftedStokesIntegral_continuous F hFcont C hFC hC T hT).comp
      continuous_subtype_val
  have hforce : Continuous (fun t : RegularizedMildTimeInterval T => forcedForceDuhamel h t.1) :=
    (continuous_forcedForceDuhamel hh hH).comp continuous_subtype_val
  exact ⟨fun t => forcedMildRHS b h F t.1 t.2.1, (hheat.sub hstokes).add hforce⟩

theorem forcedMildMap_apply (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    forcedMildMap ρ ε hε b hh hH hR T hT u t =
      forcedMildRHS b h (forcedTensorCurve ρ ε hε R T hT u) t.1 t.2.1 := rfl

/-- The Stokes Duhamel integrand of a bounded tensor curve is integrable. -/
theorem integrableOn_regularizedMildStokesIntegrand {F : ℝ → RealTensorL2}
    (hF : StronglyMeasurable F) {t C : ℝ} (ht : 0 ≤ t) (hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ C) :
    IntegrableOn (regularizedMildStokesIntegrand F t) (Ioc 0 t) := by
  obtain ⟨Fh, hFh, hrepF⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume)
    (forcedFourierTensorCurve F) (stronglyMeasurable_forcedFourierTensorCurve hF)
  have h := integrableOn_forcedFourierStokesIntegrand hFh.measurable hrepF ht
    (fun s hs => (norm_forcedFourierTensorCurve_le F s).trans (hFC s hs))
  refine (forcedRealInverse.integrable_comp h).congr (Eventually.of_forall fun s => ?_)
  exact forcedRealInverse_stokesIntegrand F t s

/-- The difference of Stokes Duhamel integrals of two tensor curves whose
difference grows at most exponentially is bounded by the weighted Abel
integral. -/
theorem norm_regularizedMildStokesIntegral_sub_le {F₁ F₂ : ℝ → RealTensorL2}
    (hF₁ : StronglyMeasurable F₁) (hF₂ : StronglyMeasurable F₂) {t C M lam : ℝ} (ht : 0 ≤ t)
    (hFC₁ : ∀ s ∈ Ioc 0 t, ‖F₁ s‖ ≤ C) (hFC₂ : ∀ s ∈ Ioc 0 t, ‖F₂ s‖ ≤ C)
    (hdiff : ∀ s ∈ Ioc 0 t, ‖F₁ s - F₂ s‖ ≤ M * Real.exp (lam * s)) :
    ‖regularizedMildStokesIntegral F₁ t - regularizedMildStokesIntegral F₂ t‖ ≤
      M / Real.sqrt (2 * Real.exp 1) *
        ∫ s in Ioc 0 t, (t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * s) := by
  have hI₁ := integrableOn_regularizedMildStokesIntegrand hF₁ ht hFC₁
  have hI₂ := integrableOn_regularizedMildStokesIntegrand hF₂ ht hFC₂
  have hg : IntegrableOn (fun s => (t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * s)) (Ioc 0 t) :=
    (integrableOn_abelKernel t ht).mul_continuousOn_of_subset
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  unfold regularizedMildStokesIntegral
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← integral_sub hI₁ hI₂,
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  unfold regularizedMildStokesIntegrand
  by_cases hst : s < t
  · rw [dite_eq_left hst, dite_eq_left hst, ← realStokesContinuousLinearMap_apply,
      ← realStokesContinuousLinearMap_apply, ← map_sub, realStokesContinuousLinearMap_apply]
    refine (realStokesOperator_norm_le (sub_pos.2 hst) _).trans ?_
    rw [stokes_kernel_eq_rpow (sub_pos.2 hst)]
    have hk : 0 ≤ (t - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_pos.2 hst).le _
    calc 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) * ‖F₁ s - F₂ s‖
        ≤ 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) *
            (M * Real.exp (lam * s)) := by gcongr; exact hdiff s hs
      _ = M / Real.sqrt (2 * Real.exp 1) * ((t - s) ^ (-(1 / 2 : ℝ)) *
            Real.exp (lam * s)) := by ring
  · rw [dite_eq_right hst, dite_eq_right hst, sub_zero, norm_zero]
    have hst' : s = t := le_antisymm hs.2 (not_lt.1 hst)
    rw [hst', sub_self, Real.zero_rpow (by norm_num), zero_mul, mul_zero]

/-- Multiplication of a curve on `[0, T]` by the exponential weight `e^{λt}`. -/
@[expose]
def forcedExpWeight (lam T : ℝ) (v : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    C(RegularizedMildTimeInterval T, RealVectorL2) :=
  ⟨fun t => Real.exp (lam * t.1) • v t,
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul v.continuous⟩

theorem forcedExpWeight_apply (lam T : ℝ) (v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (t : RegularizedMildTimeInterval T) :
    forcedExpWeight lam T v t = Real.exp (lam * t.1) • v t := rfl

theorem forcedExpWeight_neg_cancel (lam T : ℝ)
    (v : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    forcedExpWeight (-lam) T (forcedExpWeight lam T v) = v := by
  ext1 t
  rw [forcedExpWeight_apply, forcedExpWeight_apply, smul_smul, ← Real.exp_add]
  simp

theorem forcedExpWeight_cancel_neg (lam T : ℝ)
    (v : C(RegularizedMildTimeInterval T, RealVectorL2)) :
    forcedExpWeight lam T (forcedExpWeight (-lam) T v) = v := by
  ext1 t
  rw [forcedExpWeight_apply, forcedExpWeight_apply, smul_smul, ← Real.exp_add]
  simp

/-- The weighted Lipschitz estimate for the truncated forced mild map. -/
theorem norm_forcedMildMap_weighted_sub_le (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (μ := (volume : Measure ℝ))
      (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) {lam : ℝ} (hlam : 0 < lam)
    (v₁ v₂ : C(RegularizedMildTimeInterval T, RealVectorL2)) (t : RegularizedMildTimeInterval T) :
    ‖forcedExpWeight (-lam) T (forcedMildMap ρ ε hε b hh hH hR T hT (forcedExpWeight lam T v₁)) t -
        forcedExpWeight (-lam) T
          (forcedMildMap ρ ε hε b hh hH hR T hT (forcedExpWeight lam T v₂)) t‖ ≤
      4 * regularizedMildMollifierConstant ρ ε * R / Real.sqrt (2 * Real.exp 1) *
        (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) * ‖v₁ - v₂‖ := by
  set K := regularizedMildMollifierConstant ρ ε with hKdef
  have hK : 0 ≤ K := (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε)
  set F₁ := forcedTensorCurve ρ ε hε R T hT (forcedExpWeight lam T v₁) with hF₁
  set F₂ := forcedTensorCurve ρ ε hε R T hT (forcedExpWeight lam T v₂) with hF₂
  set M := 4 * K * R * ‖v₁ - v₂‖ with hM
  have hdiff : ∀ s ∈ Ioc 0 t.1, ‖F₁ s - F₂ s‖ ≤ M * Real.exp (lam * s) := by
    intro s hs
    have hsT : s ∈ RegularizedMildTimeInterval T := ⟨hs.1.le, hs.2.trans t.2.2⟩
    have hclamp := regularizedMildTimeClamp_eq_of_mem T hT hsT
    refine (norm_forcedTruncTensor_sub_le ρ ε hε hR _ _).trans ?_
    rw [hclamp, forcedExpWeight_apply, forcedExpWeight_apply, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hv : ‖v₁ ⟨s, hsT⟩ - v₂ ⟨s, hsT⟩‖ ≤ ‖v₁ - v₂‖ := by
      simpa using (v₁ - v₂).norm_coe_le_norm ⟨s, hsT⟩
    have he : 0 ≤ Real.exp (lam * s) := (Real.exp_pos _).le
    calc 4 * K * R * (Real.exp (lam * s) * ‖v₁ ⟨s, hsT⟩ - v₂ ⟨s, hsT⟩‖)
        ≤ 4 * K * R * (Real.exp (lam * s) * ‖v₁ - v₂‖) := by gcongr
      _ = M * Real.exp (lam * s) := by rw [hM]; ring
  have hC : ∀ (u : C(RegularizedMildTimeInterval T, RealVectorL2)) s,
      ‖forcedTensorCurve ρ ε hε R T hT u s‖ ≤ K * R ^ 2 := fun u s =>
    norm_forcedTensorCurve_le ρ ε hε hR T hT u s
  have hstokes := norm_regularizedMildStokesIntegral_sub_le
    (continuous_forcedTensorCurve ρ ε hε hR T hT _).stronglyMeasurable
    (continuous_forcedTensorCurve ρ ε hε hR T hT _).stronglyMeasurable t.2.1
    (fun s _ => hC _ s) (fun s _ => hC _ s) hdiff
  rw [forcedExpWeight_apply, forcedExpWeight_apply, ← smul_sub, forcedMildMap_apply,
    forcedMildMap_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsub : forcedMildRHS b h F₁ t.1 t.2.1 - forcedMildRHS b h F₂ t.1 t.2.1 =
      -(regularizedMildStokesIntegral F₁ t.1 - regularizedMildStokesIntegral F₂ t.1) := by
    unfold forcedMildRHS
    abel
  rw [← hF₁, ← hF₂, hsub, norm_neg]
  have hexp : Real.exp (-lam * t.1) *
      ∫ s in Ioc 0 t.1, (t.1 - s) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * s) =
      ∫ s in Ioc 0 t.1, (t.1 - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * (t.1 - s)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [show -lam * (t.1 - s) = -lam * t.1 + lam * s by ring, Real.exp_add]
    ring
  have hgamma := integral_abelKernel_exp_le hlam t.2.1
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hsq : 0 ≤ M / Real.sqrt (2 * Real.exp 1) := by positivity
  calc Real.exp (-lam * t.1) *
        ‖regularizedMildStokesIntegral F₁ t.1 - regularizedMildStokesIntegral F₂ t.1‖
      ≤ Real.exp (-lam * t.1) * (M / Real.sqrt (2 * Real.exp 1) *
          ∫ s in Ioc 0 t.1, (t.1 - s) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * s)) :=
        mul_le_mul_of_nonneg_left hstokes (Real.exp_pos _).le
    _ = M / Real.sqrt (2 * Real.exp 1) * (Real.exp (-lam * t.1) *
          ∫ s in Ioc 0 t.1, (t.1 - s) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * s)) := by ring
    _ ≤ M / Real.sqrt (2 * Real.exp 1) * (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_left hgamma hsq
    _ = 4 * K * R / Real.sqrt (2 * Real.exp 1) *
        (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) * ‖v₁ - v₂‖ := by rw [hM]; ring

/-- A weight exponent making the weighted map a contraction with constant
`1/2`. -/
theorem exists_forcedWeight (A : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ A * lam ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
  refine ⟨(2 * A) ^ 2 + 1, by positivity, ?_⟩
  have hpos : 0 < (2 * A) ^ 2 + 1 := by positivity
  rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
  have hsq : 2 * A ≤ Real.sqrt ((2 * A) ^ 2 + 1) :=
    Real.le_sqrt_of_sq_le (by linarith only [])
  have hs : 0 < Real.sqrt ((2 * A) ^ 2 + 1) := Real.sqrt_pos.2 hpos
  rw [← div_eq_mul_inv, div_le_iff₀ hs]
  linarith only [hsq]

/-- The truncated forced mild map has a unique fixed point among continuous
curves on `[0, T]`. -/
theorem forcedMildMap_existsUnique_fixedPoint (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) {h : ℝ → RealVectorL2} (hh : StronglyMeasurable h)
    (hH : ∀ T : ℝ, IntegrableOn (μ := (volume : Measure ℝ))
      (fun s => ‖h s‖) (Ioc 0 T)) {R : ℝ} (hR : 0 ≤ R)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ u : C(RegularizedMildTimeInterval T, RealVectorL2),
      forcedMildMap ρ ε hε b hh hH hR T hT u = u ∧
      ∀ u' : C(RegularizedMildTimeInterval T, RealVectorL2),
        forcedMildMap ρ ε hε b hh hH hR T hT u' = u' → u' = u := by
  set A := 4 * regularizedMildMollifierConstant ρ ε * R / Real.sqrt (2 * Real.exp 1) *
    Real.Gamma (1 / 2) with hAdef
  have hA : 0 ≤ A := by
    have := (ENNReal.toReal_nonneg : 0 ≤ regularizedMildMollifierConstant ρ ε)
    have hΓ : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    positivity
  obtain ⟨lam, hlam, hlamA⟩ := exists_forcedWeight A
  let Φ := forcedMildMap ρ ε hε b hh hH hR T hT
  let Ψ : C(RegularizedMildTimeInterval T, RealVectorL2) →
      C(RegularizedMildTimeInterval T, RealVectorL2) :=
    fun v => forcedExpWeight (-lam) T (Φ (forcedExpWeight lam T v))
  have hΨ : ContractingWith (1 / 2 : NNReal) Ψ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun v₁ v₂ => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
    rw [ContinuousMap.sub_apply]
    refine (norm_forcedMildMap_weighted_sub_le ρ ε hε b hh hH hR T hT hlam v₁ v₂ t).trans ?_
    have hcoef : 4 * regularizedMildMollifierConstant ρ ε * R / Real.sqrt (2 * Real.exp 1) *
        (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) = A * lam ^ (-(1 / 2 : ℝ)) := by
      rw [hAdef]; ring
    rw [hcoef]
    have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hlamA (norm_nonneg _)
  let v := ContractingWith.fixedPoint Ψ hΨ
  have hv : Ψ v = v := ContractingWith.fixedPoint_isFixedPt hΨ
  refine ⟨forcedExpWeight lam T v, ?_, fun u' hu' => ?_⟩
  · have h1 := congrArg (forcedExpWeight lam T) hv
    simp only [Ψ, forcedExpWeight_cancel_neg] at h1
    exact h1
  · have hfix : Ψ (forcedExpWeight (-lam) T u') = forcedExpWeight (-lam) T u' := by
      simp only [Ψ, forcedExpWeight_cancel_neg]
      change forcedExpWeight (-lam) T (forcedMildMap ρ ε hε b hh hH hR T hT u') = _
      rw [hu']
    have huniq := ContractingWith.fixedPoint_unique hΨ hfix
    have h2 := congrArg (forcedExpWeight lam T) huniq
    rw [forcedExpWeight_cancel_neg] at h2
    exact h2

end CKN.Leray

end
