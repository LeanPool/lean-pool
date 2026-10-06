/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Inverse Fourier integrals of weighted square-integrable fields

For the pointwise realization in `thm:regularised` (R2), a spatial field is
represented by the inverse Fourier integral of its Fourier transform. When
the transform is an inverse Bessel weight of order four times a
square-integrable field, it is integrable against every polynomial weight of
degree at most two. The inverse Fourier integral is then continuous,
differentiable with the derivative given by multiplication in frequency, and
represents the `L²` inverse Fourier transform.
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real SchwartzMap ContDiff

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The directional derivative of the inverse Fourier integral. -/
theorem regR12_fourierInv_fderiv_apply {h : L2Vec3 → E}
    (hh : Integrable h) (hh1 : Integrable (fun v => ‖v‖ * ‖h v‖)) (x e : L2Vec3) :
    HasFDerivAt (𝓕⁻ h) (fderiv ℝ (𝓕⁻ h) x) x ∧
      fderiv ℝ (𝓕⁻ h) x e =
        𝓕⁻ (fun v => ((2 * π * inner ℝ v e : ℝ) * I) • h v) x := by
  have hfun : (𝓕⁻ h) = fun w => 𝓕 h (-w) := funext fun w => Real.fourierInv_eq_fourier_neg h w
  have hF := Real.hasFDerivAt_fourier hh hh1 (-x)
  have hcomp : HasFDerivAt (fun w => 𝓕 h (-w))
      ((𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) h) (-x)).comp
        (-(ContinuousLinearMap.id ℝ L2Vec3))) x := by
    exact hF.comp x (hasFDerivAt_id x).neg
  rw [hfun]
  refine ⟨hcomp.differentiableAt.hasFDerivAt, ?_⟩
  rw [hcomp.fderiv]
  have hInt : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) h) := by
    refine Integrable.mono' (hh1.const_mul (2 * π * ‖(innerSL ℝ : L2Vec3 →L[ℝ] L2Vec3 →L[ℝ] ℝ)‖))
      hh.1.fourierSMulRight ?_
    filter_upwards with v
    have := VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) h v
    calc _ ≤ _ := this
      _ = _ := by ring
  have happ : (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) h) (-x)) (-e) =
      𝓕 (fun v => VectorFourier.fourierSMulRight (innerSL ℝ) h v (-e)) (-x) := by
    rw [Real.fourier_eq, Real.fourier_eq, ContinuousLinearMap.integral_apply]
    · rfl
    · refine (hInt.norm.mono' ?_ ?_)
      · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
          hInt.1
      · filter_upwards with v
        rw [Circle.norm_smul]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply]
  rw [happ, ← Real.fourierInv_eq_fourier_neg]
  refine congrArg (fun f : L2Vec3 → E => 𝓕⁻ f x) (funext fun v => ?_)
  rw [VectorFourier.fourierSMulRight_apply, innerSL_apply_apply, inner_neg_right,
    ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- The inverse Fourier integral is bounded by the `L¹` norm. -/
theorem regR12_norm_fourierInv_le (h : L2Vec3 → E) (hh : AEStronglyMeasurable h) (x : L2Vec3) :
    ‖𝓕⁻ h x‖ ≤ (eLpNorm h 1 volume).toReal := by
  rw [Real.fourierInv_eq]
  calc ‖∫ v, 𝐞 (inner ℝ v x) • h v‖ ≤ ∫ v, ‖𝐞 (inner ℝ v x) • h v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, ‖h v‖ := by simp_rw [Circle.norm_smul]
    _ = (eLpNorm h 1 volume).toReal := by
        rw [integral_norm_eq_lintegral_enorm hh, eLpNorm_one_eq_lintegral_enorm]
        exact hh

/-- The inverse Fourier integral is additive on integrable fields. -/
theorem regR12_fourierInv_sub (h₁ h₂ : L2Vec3 → E) (hh₁ : Integrable h₁) (hh₂ : Integrable h₂)
    (x : L2Vec3) :
    𝓕⁻ (fun v => h₁ v - h₂ v) x = 𝓕⁻ h₁ x - 𝓕⁻ h₂ x := by
  have hi : ∀ g : L2Vec3 → E, Integrable g → Integrable (fun v => 𝐞 (inner ℝ v x) • g v) := by
    intro g hg
    refine hg.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul hg.1
    · rw [Circle.norm_smul]
  simp only [Real.fourierInv_eq, smul_sub]
  exact integral_sub (hi h₁ hh₁) (hi h₂ hh₂)

/-- The inverse Fourier integral of an integrable field is continuous. -/
theorem regR12_fourierInv_continuous (h : L2Vec3 → E) (hh : Integrable h) :
    Continuous (𝓕⁻ h) := by
  have h1 : MemLp h 1 volume := memLp_one_iff_integrable.2 hh
  rw [← Real.Lp.fourierTransformInv_toLp h1]
  exact (Real.Lp.fourierTransformInv h1.toLp).continuous

end Derivative

section Representation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The pairing of the inverse Fourier integral of an integrable field with a
Schwartz function. -/
theorem regR12_integral_smul_fourierInv (h : L2Vec3 → E) (hh : Integrable h)
    (φ : 𝓢(L2Vec3, ℂ)) :
    ∫ x, φ x • 𝓕⁻ h x = ∫ ξ, 𝓕⁻ (φ : L2Vec3 → ℂ) ξ • h ξ := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ L2Vec3)
    Real.continuous_fourierChar continuous_inner.neg φ.integrable hh
  have hLflip : (-innerₗ L2Vec3).flip = -innerₗ L2Vec3 := by
    ext x y
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, innerₗ_apply_apply]
    exact congrArg Neg.neg (real_inner_comm x y)
  have hInvφ : VectorFourier.fourierIntegral 𝐞 volume (-innerₗ L2Vec3) (φ : L2Vec3 → ℂ) =
      𝓕⁻ (φ : L2Vec3 → ℂ) := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq]
    simp [VectorFourier.fourierIntegral, innerₗ_apply_apply, inner_neg_right]
  have hInvh : VectorFourier.fourierIntegral 𝐞 volume (-innerₗ L2Vec3) h = 𝓕⁻ h := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq]
    simp [VectorFourier.fourierIntegral, innerₗ_apply_apply, inner_neg_right]
  rw [hLflip, hInvφ, hInvh] at hswap
  exact hswap.symm

/-- The inverse Fourier integral of an integrable, square-integrable field
represents its `L²` inverse Fourier transform. -/
theorem regR12_fourierInv_ae_eq_L2 (h : L2Vec3 → E) (hh : Integrable h)
    (hh2 : MemLp h 2) :
    𝓕⁻ h =ᵐ[volume] ((𝓕⁻ (hh2.toLp h) : Lp E 2 (volume : Measure L2Vec3)) : L2Vec3 → E) := by
  let H : Lp E 2 (volume : Measure L2Vec3) := hh2.toLp h
  have hdist : ∀ φ : 𝓢(L2Vec3, ℂ),
      ∫ x, φ x • (𝓕⁻ H : Lp E 2 (volume : Measure L2Vec3)) x = ∫ x, φ x • 𝓕⁻ h x := by
    intro φ
    have h1 : (Lp.toTemperedDistribution (E := L2Vec3) (F := E) (μ := volume)
        (𝓕⁻ H : Lp E 2 (volume : Measure L2Vec3))) φ =
        ∫ x, φ x • (𝓕⁻ H : Lp E 2 (volume : Measure L2Vec3)) x :=
      Lp.toTemperedDistribution_apply _ _
    rw [← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
      Lp.toTemperedDistribution_apply] at h1
    rw [← h1, regR12_integral_smul_fourierInv h hh φ]
    apply integral_congr_ae
    filter_upwards [hh2.coeFn_toLp] with ξ hξ
    rw [SchwartzMap.fourierInv_coe]
    change _ • H ξ = _
    rw [hξ]
  have hloc1 : LocallyIntegrable (𝓕⁻ h) volume := by
    have h1 : MemLp h 1 volume := memLp_one_iff_integrable.2 hh
    rw [← Real.Lp.fourierTransformInv_toLp h1]
    exact (Real.Lp.fourierTransformInv h1.toLp).continuous.locallyIntegrable
  have hloc2 : LocallyIntegrable ((𝓕⁻ H : Lp E 2 (volume : Measure L2Vec3)) : L2Vec3 → E) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun g g_diff g_supp => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_supp.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have h2 := hdist (hg₁.toSchwartzMap hg₂)
  have hcoe : ∀ x, (hg₁.toSchwartzMap hg₂ : L2Vec3 → ℂ) x = (g x : ℂ) := fun x => rfl
  simp only [hcoe, Complex.coe_smul] at h2
  exact h2.symm

end Representation

section Weight

/-- The inverse Bessel weight `(1 + |ξ|²)⁻¹` of order two, square integrable
in three dimensions. -/
@[expose]
def regR12Kernel (ξ : L2Vec3) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)

theorem regR12Kernel_continuous : Continuous regR12Kernel := by
  unfold regR12Kernel
  exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'

theorem regR12Kernel_memLp : MemLp regR12Kernel 2 volume := by
  have hfin : Module.finrank ℝ L2Vec3 = 3 := by
    calc
      Module.finrank ℝ L2Vec3 = Module.finrank ℝ (Fin 3 → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).finrank_eq
      _ = 3 := by simp
  have hkMeas : AEStronglyMeasurable regR12Kernel volume :=
    regR12Kernel_continuous.aestronglyMeasurable
  rw [memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hkMeas]
  have hkernel : Integrable (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2) ^ (-4 / 2 : ℝ)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num [hfin])
  refine (hkernel.lintegral_lt_top).trans_eq' ?_
  refine lintegral_congr fun ξ => ?_
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  unfold regR12Kernel
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg hpos.le _), ENNReal.toReal_ofNat,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hpos.le _) (by norm_num),
    ← Real.rpow_mul hpos.le]
  norm_num

/-- A multiplier of at most quadratic growth, times the inverse Bessel weight
of order four, sends square-integrable fields to integrable fields. -/
theorem regR12_weighted_eLpNorm_one_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M) (C : ℝ) (hC : 0 ≤ C)
    (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G : L2Vec3 → E) (hG : AEStronglyMeasurable G) :
    eLpNorm (fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • G ξ) 1 volume ≤
      ENNReal.ofReal C * eLpNorm regR12Kernel 2 volume * eLpNorm G 2 volume := by
  have hpt : ∀ ξ, ‖M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • G ξ‖ ≤
      ‖(C * regR12Kernel ξ) • G ξ‖ := by
    intro ξ
    have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have hk : 0 ≤ regR12Kernel ξ := Real.rpow_nonneg hpos.le _
    rw [norm_smul, norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hk)]
    have halg : (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) = regR12Kernel ξ := by
      unfold regR12Kernel
      rw [show (-1 : ℝ) = 1 + (-2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    calc ‖M ξ‖ * ((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ‖G ξ‖)
        ≤ C * (1 + ‖ξ‖ ^ 2) * ((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ‖G ξ‖) :=
          mul_le_mul_of_nonneg_right (hMC ξ) (by positivity)
      _ = C * ((1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) * ‖G ξ‖ := by ring
      _ = C * regR12Kernel ξ * ‖G ξ‖ := by rw [halg]
  calc eLpNorm (fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • G ξ) 1 volume
      ≤ eLpNorm (fun ξ => (C * regR12Kernel ξ) • G ξ) 1 volume :=
        eLpNorm_mono (by
          have hwc : Continuous fun ξ : L2Vec3 =>
              (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) :=
            Complex.continuous_ofReal.comp ((continuous_const.add
               (continuous_norm.pow 2)).rpow_const fun ξ =>
                 Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
          exact hM.smul (hwc.aestronglyMeasurable.smul hG)) hpt
    _ ≤ eLpNorm (fun ξ => C * regR12Kernel ξ) 2 volume * eLpNorm G 2 volume :=
        eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          ((continuous_const.mul regR12Kernel_continuous).aestronglyMeasurable) hG
    _ = ENNReal.ofReal C * eLpNorm regR12Kernel 2 volume * eLpNorm G 2 volume := by
        rw [show (fun ξ => C * regR12Kernel ξ) = C • regR12Kernel from rfl,
          eLpNorm_const_smul, Real.enorm_of_nonneg hC]

/-- The multiplied weighted field is integrable. -/
theorem regR12_weighted_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M) (C : ℝ) (hC : 0 ≤ C)
    (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G : L2Vec3 → E) (hG : MemLp G 2 volume) :
    Integrable (fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • G ξ) := by
  rw [← memLp_one_iff_integrable]
  refine lt_of_le_of_lt (regR12_weighted_eLpNorm_one_le M hM C hC hMC G
    hG.aestronglyMeasurable) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top regR12Kernel_memLp) hG

end Weight

section WeightedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The inverse Fourier integral of a square-integrable frequency field `G`,
multiplied by `M` and the inverse Bessel weight of order four. -/
@[expose]
def regR12WeightedField (M : L2Vec3 → ℂ) (G : Lp E 2 (volume : Measure L2Vec3))
    (x : L2Vec3) : E :=
  𝓕⁻ (fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • (G : L2Vec3 → E) ξ) x

theorem regR12Weight_continuous :
    Continuous fun ξ : L2Vec3 => (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((continuous_const.add
    (continuous_norm.pow 2)).rpow_const fun _ =>
      Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')

variable (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M) (C : ℝ) (hC : 0 ≤ C)
  (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))

include hM hC hMC in
/-- The weighted field is bounded by the `L²` norm of the frequency field. -/
theorem regR12WeightedField_norm_le (G : Lp E 2 (volume : Measure L2Vec3)) (x : L2Vec3) :
    ‖regR12WeightedField M G x‖ ≤
      C * (eLpNorm regR12Kernel 2 volume).toReal * ‖G‖ := by
  refine (regR12_norm_fourierInv_le _ (hM.smul (regR12Weight_continuous.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable G))) x).trans ?_
  have hb := regR12_weighted_eLpNorm_one_le M hM C hC hMC (G : L2Vec3 → E)
    (Lp.aestronglyMeasurable G)
  have hfin : ENNReal.ofReal C * eLpNorm regR12Kernel 2 volume *
      eLpNorm (G : L2Vec3 → E) 2 volume ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top regR12Kernel_memLp)
      (Lp.memLp G)).ne
  refine (ENNReal.toReal_mono hfin hb).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, Lp.norm_def]

include hM hC hMC in
/-- The weighted field is linear in the frequency field. -/
theorem regR12WeightedField_sub (G H : Lp E 2 (volume : Measure L2Vec3)) (x : L2Vec3) :
    regR12WeightedField M G x - regR12WeightedField M H x = regR12WeightedField M (G - H) x := by
  unfold regR12WeightedField
  rw [← regR12_fourierInv_sub _ _
    (regR12_weighted_integrable M hM C hC hMC _ (Lp.memLp G))
    (regR12_weighted_integrable M hM C hC hMC _ (Lp.memLp H))]
  apply Real.fourierInv_congr_ae
  filter_upwards [Lp.coeFn_sub G H] with ξ hξ
  rw [hξ, Pi.sub_apply, smul_sub, smul_sub]

include hM hC hMC in
/-- The weighted field is jointly continuous in the frequency field and the
spatial point. -/
theorem regR12WeightedField_continuous :
    Continuous (fun p : Lp E 2 (volume : Measure L2Vec3) × L2Vec3 =>
      regR12WeightedField M p.1 p.2) := by
  have hK : 0 ≤ C * (eLpNorm regR12Kernel 2 volume).toReal := by positivity
  refine continuous_prod_of_continuous_lipschitzWith _ ⟨_, hK⟩ ?_ ?_
  · intro G
    exact regR12_fourierInv_continuous _
      (regR12_weighted_integrable M hM C hC hMC _ (Lp.memLp G))
  · intro x
    refine LipschitzWith.of_dist_le_mul fun G H => ?_
    rw [dist_eq_norm, dist_eq_norm, regR12WeightedField_sub M hM C hC hMC]
    exact regR12WeightedField_norm_le M hM C hC hMC (G - H) x

/-- The frequency multiplier `2πi⟨ξ, e⟩` of the directional derivative along `e`. -/
@[expose]
def regR12DirSymbol (e ξ : L2Vec3) : ℂ := ((2 * π * inner ℝ ξ e : ℝ) : ℂ) * I

theorem regR12DirSymbol_continuous (e : L2Vec3) : Continuous (regR12DirSymbol e) := by
  unfold regR12DirSymbol
  fun_prop

theorem regR12DirSymbol_norm_le (e ξ : L2Vec3) :
    ‖regR12DirSymbol e ξ‖ ≤ 2 * π * ‖e‖ * ‖ξ‖ := by
  unfold regR12DirSymbol
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc |2 * π * inner ℝ ξ e| = 2 * π * |inner ℝ ξ e| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    _ ≤ 2 * π * (‖ξ‖ * ‖e‖) := by gcongr; exact abs_real_inner_le_norm ξ e
    _ = 2 * π * ‖e‖ * ‖ξ‖ := by ring

include hM hC hMC in
/-- The weighted field is differentiable when the multiplier grows at most
linearly, and its directional derivative multiplies the frequency field by
`2πi⟨ξ, e⟩`. -/
theorem regR12WeightedField_fderiv_apply
    (hMC1 : ∀ ξ, ‖ξ‖ * ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G : Lp E 2 (volume : Measure L2Vec3)) (x e : L2Vec3) :
    HasFDerivAt (regR12WeightedField M G) (fderiv ℝ (regR12WeightedField M G) x) x ∧
      fderiv ℝ (regR12WeightedField M G) x e =
        regR12WeightedField (fun ξ => regR12DirSymbol e ξ * M ξ) G x := by
  have hint := regR12_weighted_integrable M hM C hC hMC _ (Lp.memLp G)
  have hint1 : Integrable (fun v : L2Vec3 =>
      ‖v‖ * ‖M v • (((1 + ‖v‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • (G : L2Vec3 → E) v‖) := by
    have h := (regR12_weighted_integrable (fun ξ => (‖ξ‖ : ℂ) * M ξ)
      ((Complex.continuous_ofReal.comp continuous_norm).aestronglyMeasurable.mul hM) C hC
      (fun ξ => by rw [norm_mul, Complex.norm_real, norm_norm]; exact hMC1 ξ) _
      (Lp.memLp G)).norm
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [norm_smul, norm_mul, Complex.norm_real, norm_norm]
    ring
  obtain ⟨hd, hformula⟩ := regR12_fourierInv_fderiv_apply hint hint1 x e
  have hfun : regR12WeightedField M G = 𝓕⁻ (fun ξ =>
      M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • (G : L2Vec3 → E) ξ) := rfl
  rw [hfun]
  refine ⟨hd, ?_⟩
  rw [hformula]
  unfold regR12WeightedField regR12DirSymbol
  refine congrArg (fun f : L2Vec3 → E => 𝓕⁻ f x) (funext fun v => ?_)
  rw [smul_smul]

end WeightedField

section WeightedRepresentation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The weighted field represents every `L²` field whose Fourier transform is
the weighted frequency field. -/
theorem regR12WeightedField_ae_eq (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M) (C : ℝ)
    (hC : 0 ≤ C) (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G H : Lp E 2 (volume : Measure L2Vec3))
    (hGH : ((Lp.fourierTransformₗᵢ L2Vec3 E H : Lp E 2 (volume : Measure L2Vec3)) :
      L2Vec3 → E) =ᵐ[volume]
        fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) • (G : L2Vec3 → E) ξ) :
    regR12WeightedField M G =ᵐ[volume] (H : L2Vec3 → E) := by
  let h : L2Vec3 → E := fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
    (G : L2Vec3 → E) ξ
  have hint : Integrable h := regR12_weighted_integrable M hM C hC hMC _ (Lp.memLp G)
  have hL2 : MemLp h 2 volume := by
    have h2 : MemLp h 2 volume := (Lp.memLp (Lp.fourierTransformₗᵢ L2Vec3 E H)).ae_eq hGH
    exact h2
  have hrep := regR12_fourierInv_ae_eq_L2 h hint hL2
  have hLp : hL2.toLp h = Lp.fourierTransformₗᵢ L2Vec3 E H := by
    apply Lp.ext
    filter_upwards [hL2.coeFn_toLp, hGH] with ξ h1 h2
    rw [h1, h2]
  rw [hLp] at hrep
  have hinv : (𝓕⁻ (Lp.fourierTransformₗᵢ L2Vec3 E H : Lp E 2 (volume : Measure L2Vec3)) :
      Lp E 2 (volume : Measure L2Vec3)) = H := by
    change (Lp.fourierTransformₗᵢ L2Vec3 E).symm (Lp.fourierTransformₗᵢ L2Vec3 E H) = H
    exact LinearIsometryEquiv.symm_apply_apply _ _
  rw [hinv] at hrep
  exact hrep

end WeightedRepresentation

end CKN.Leray
