/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierGeneral
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Iterated spatial derivatives of the regularizing convolution

The coordinate derivatives in `lem:reg-mollifier-bounds` are evaluations of
the iterated Fréchet derivative on tuples of coordinate vectors.
-/

public section

open MeasureTheory
open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Scalar multiplication as a bilinear map on the real vector `L²` space. -/
@[expose]
def allDerivativeScalarVectorActionLinear : ℝ →ₗ[ℝ]
    L2Vec3 →ₗ[ℝ] L2Vec3 :=
  LinearMap.mk₂ ℝ (fun c x => c • x)
    (by intro c d x; exact add_smul c d x)
    (by intro c d x; exact mul_smul c d x)
    (by intro c x y; exact smul_add c x y)
    (by intro c d x; exact (smul_comm c d x).symm)

/-- The continuous bilinear scalar action on the real vector `L²` space. -/
@[expose]
def allDerivativeScalarVectorAction : ℝ →L[ℝ]
    L2Vec3 →L[ℝ] L2Vec3 :=
  allDerivativeScalarVectorActionLinear.mkContinuous₂ 1 (by
    intro c x
    change ‖c • x‖ ≤ 1 * ‖c‖ * ‖x‖
    simpa [one_mul] using norm_smul_le c x)

/-- A smooth compactly supported scalar kernel differentiates through vector
convolution under local integrability. -/
theorem allDerivativeScalarVectorConvolution_hasFDerivAt
    (k : L2Vec3 → ℝ) (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k)
    {f : L2Vec3 → L2Vec3} (hf : LocallyIntegrable f volume)
    (x : L2Vec3) :
    HasFDerivAt
      (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume)
      ((MeasureTheory.convolution (fderiv ℝ k) f
        (allDerivativeScalarVectorAction.precompL L2Vec3) volume) x) x := by
  exact hkc.hasFDerivAt_convolution_left
    (L := allDerivativeScalarVectorAction) hk hf x

/-- The derivative of vector convolution is convolution with the directional
derivative of the scalar kernel. -/
theorem allDerivativeScalarVectorConvolution_directional_deriv
    (k : L2Vec3 → ℝ) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    {f : L2Vec3 → L2Vec3} (hf : LocallyIntegrable f volume)
    (x v : L2Vec3) :
    (fderiv ℝ
      (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) x) v =
        ∫ y : L2Vec3, (fderiv ℝ k y) v • f (x - y) := by
  have hconv : ConvolutionExists (fderiv ℝ k) f
      (allDerivativeScalarVectorAction.precompL L2Vec3) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := L2Vec3) (E := L2Vec3 →L[ℝ] ℝ) (E' := L2Vec3)
      (F := L2Vec3 →L[ℝ] L2Vec3)
      (allDerivativeScalarVectorAction.precompL L2Vec3)
      (hkc.fderiv (𝕜 := ℝ))
      (hk.continuous_fderiv (by norm_num)) hf
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hD := allDerivativeScalarVectorConvolution_hasFDerivAt k hk1 hkc hf x
  rw [hD.fderiv]
  change ((MeasureTheory.convolution (fderiv ℝ k) f
      (allDerivativeScalarVectorAction.precompL L2Vec3) volume) x) v = _
  rw [MeasureTheory.convolution,
    ContinuousLinearMap.integral_apply (hconv x) v]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [ContinuousLinearMap.precompL_apply, allDerivativeScalarVectorAction,
    allDerivativeScalarVectorActionLinear]

private theorem allDerivativeScalarVectorConvolution_iterated
    (n : ℕ) (v : Fin n → L2Vec3) (k : L2Vec3 → ℝ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    {f : L2Vec3 → L2Vec3} (hf : LocallyIntegrable f volume)
    (x : L2Vec3) :
    (iteratedFDeriv ℝ n
      (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) x) v =
        ∫ y : L2Vec3, (iteratedFDeriv ℝ n k y) v • f (x - y) := by
  induction n generalizing k x with
  | zero =>
      change (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) x = _
      rfl
  | succ n ih =>
      have hkTail : ContDiff ℝ (⊤ : ℕ∞) k := hk
      let kTail : L2Vec3 → ℝ := fun y => (iteratedFDeriv ℝ n k y) (Fin.tail v)
      have hkTailCont : ContDiff ℝ 2 kTail := by
        have hIter : ContDiff ℝ 2 (iteratedFDeriv ℝ n k) := by
          have hNat : ContDiff ℝ (2 + n) k := hkTail.of_le (by simp)
          exact hNat.iteratedFDeriv_right' (m := 2) (i := n)
        change ContDiff ℝ 2 (fun y => (iteratedFDeriv ℝ n k y) (Fin.tail v))
        exact hIter.continuousLinearMap_comp (ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin n => L2Vec3) ℝ (Fin.tail v))
      have hkTailCompact : HasCompactSupport kTail := by
        have hIter : HasCompactSupport (iteratedFDeriv ℝ n k) := hkc.iteratedFDeriv n
        apply HasCompactSupport.of_support_subset_isCompact hIter.isCompact
        intro y hy
        simp only [Function.mem_support] at hy
        by_contra hnot
        have hz : iteratedFDeriv ℝ n k y = 0 :=
          image_eq_zero_of_notMem_tsupport (f := iteratedFDeriv ℝ n k) hnot
        exact hy (by simp [kTail, hz])
      have hIHfun : (fun z : L2Vec3 =>
          (iteratedFDeriv ℝ n
            (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) z)
              (Fin.tail v)) =
          MeasureTheory.convolution kTail f allDerivativeScalarVectorAction volume := by
        funext z
        have h := ih (Fin.tail v) k hkTail hkc z
        simpa [MeasureTheory.convolution, kTail, allDerivativeScalarVectorAction,
          allDerivativeScalarVectorActionLinear, smul_eq_mul] using h
      have hconvD := allDerivativeScalarVectorConvolution_directional_deriv
        kTail hkTailCont hkTailCompact hf x (v 0)
      have hconvSmooth : ContDiff ℝ (⊤ : ℕ∞)
          (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) :=
        hkc.contDiff_convolution_left (n := ⊤) (L := allDerivativeScalarVectorAction)
          hk hf
      have hconvDiff : DifferentiableAt ℝ
          (iteratedFDeriv ℝ n
            (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume)) x :=
        hconvSmooth.contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top n)
      rw [hconvDiff.iteratedFDeriv_succ_apply_left' (m := v)]
      rw [hIHfun]
      rw [hconvD]
      apply integral_congr_ae
      filter_upwards [] with y
      have hderiv : (fderiv ℝ kTail y) (v 0) = (iteratedFDeriv ℝ (n + 1) k y) v := by
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n k) y :=
          hkTail.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast ENat.natCast_lt_top n)
        symm
        simpa [kTail] using hdiff.iteratedFDeriv_succ_apply_left' (m := v)
      rw [hderiv]

/-- The dilated kernel derivative in any ordered set of directions has the
exact three-dimensional `L²` scaling for `lem:reg-mollifier-bounds`. -/
theorem regMollifierKernel_iteratedDerivative_eLpNorm_two
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (v : Fin n → L2Vec3) :
    eLpNorm (fun y : L2Vec3 =>
        (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v) 2 volume =
      ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ) - (n : ℝ))) *
        eLpNorm (fun y : L2Vec3 => (iteratedFDeriv ℝ n ρ.rho y) v) 2 volume := by
  let dε : L2Vec3 → ℝ := fun y =>
    (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v
  let dρ : L2Vec3 → ℝ := fun y => (iteratedFDeriv ℝ n ρ.rho y) v
  let c : ℝ := (ε ^ 3)⁻¹ * (ε⁻¹) ^ n
  have hscaleMap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => ε⁻¹ • y) := by fun_prop
  have hprofileScaled : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => ρ.rho (ε⁻¹ • y)) := ρ.smooth.comp hscaleMap
  have hkernelSmooth : ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : L2Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact contDiff_const.mul hprofileScaled
  have hkernelCompact : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have h := ρ.compact.comp_homeomorph (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    change HasCompactSupport (fun y => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact h.mul_left
  have hiterScale (y : L2Vec3) :
      (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) =
        c • iteratedFDeriv ℝ n ρ.rho (ε⁻¹ • y) := by
    have hprofileScaledN : ContDiff ℝ (n : ℕ∞)
        (fun z : L2Vec3 => ρ.rho (ε⁻¹ • z)) :=
      hprofileScaled.of_le (by simp)
    have hconst := iteratedFDeriv_const_smul_apply
      (f := fun z : L2Vec3 => ρ.rho (ε⁻¹ • z))
      (i := n) (x := y) (a := (ε ^ 3)⁻¹) hprofileScaledN.contDiffAt
    have hcomp := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (a := ε⁻¹)
      (f := ρ.rho) (i := n) (ρ.smooth.of_le (by simp))
    change iteratedFDeriv ℝ n
      (fun z : L2Vec3 => (ε ^ 3)⁻¹ • ρ.rho (ε⁻¹ • z)) y = _
    calc
      _ = (ε ^ 3)⁻¹ •
            iteratedFDeriv ℝ n (fun z : L2Vec3 => ρ.rho (ε⁻¹ • z)) y := hconst
      _ = (ε ^ 3)⁻¹ •
            ((ε⁻¹) ^ n • iteratedFDeriv ℝ n ρ.rho (ε⁻¹ • y)) := by rw [hcomp]
      _ = c • iteratedFDeriv ℝ n ρ.rho (ε⁻¹ • y) := by
            simp [c, smul_smul]
  have hpoint (y : L2Vec3) : dε y = c * dρ (ε⁻¹ • y) := by
    dsimp [dε, dρ]
    rw [hiterScale]
    simp only [smul_apply, smul_eq_mul]
  have hcpos : 0 < c := by positivity
  have hiterContinuous : Continuous (fun y : L2Vec3 =>
      iteratedFDeriv ℝ n ρ.rho y) :=
    ρ.smooth.continuous_iteratedFDeriv (by simp)
  have hρcont : Continuous dρ := by
    dsimp [dρ]
    exact (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => L2Vec3) ℝ v).continuous.comp hiterContinuous
  have hρcompact : HasCompactSupport dρ := by
    have hiter : HasCompactSupport (iteratedFDeriv ℝ n ρ.rho) :=
      ρ.compact.iteratedFDeriv n
    apply HasCompactSupport.of_support_subset_isCompact hiter.isCompact
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hnot
    have hz : iteratedFDeriv ℝ n ρ.rho y = 0 :=
      image_eq_zero_of_notMem_tsupport (f := iteratedFDeriv ℝ n ρ.rho) hnot
    exact hy (by simp [dρ, hz])
  have hkernelIterContinuous : Continuous (fun y : L2Vec3 =>
      iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) :=
    hkernelSmooth.continuous_iteratedFDeriv (by simp)
  have hεcont : Continuous dε := by
    dsimp [dε]
    exact (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => L2Vec3) ℝ v).continuous.comp hkernelIterContinuous
  have hεcompact : HasCompactSupport dε := by
    have hiter : HasCompactSupport
        (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε)) :=
      hkernelCompact.iteratedFDeriv n
    apply HasCompactSupport.of_support_subset_isCompact hiter.isCompact
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hnot
    have hz : iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε)) hnot
    exact hy (by simp [dε, hz])
  have hρmem : MemLp dρ (2 : ℝ≥0∞) volume :=
    hρcont.memLp_of_hasCompactSupport hρcompact
  have hεmem : MemLp dε (2 : ℝ≥0∞) volume :=
    hεcont.memLp_of_hasCompactSupport hεcompact
  have hchange :
      ∫ y : L2Vec3, ‖dρ (ε⁻¹ • y)‖ ^ 2 =
        |ε ^ Module.finrank ℝ L2Vec3| * ∫ y : L2Vec3, ‖dρ y‖ ^ 2 := by
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_inv_smul (μ := volume)
        (f := fun y => ‖dρ y‖ ^ 2) ε)
  have hdim : Module.finrank ℝ L2Vec3 = 3 := by
    calc
      Module.finrank ℝ L2Vec3 = Module.finrank ℝ (Fin 3 → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).finrank_eq
      _ = Fintype.card (Fin 3) := Module.finrank_pi ℝ
      _ = 3 := by simp
  have hcSq : c ^ 2 * ε ^ 3 = ε ^ (-((3 + 2 * n : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hpow : ε ^ (3 + 2 * n) = ε ^ 3 * (ε ^ n) ^ 2 := by
      rw [pow_add, show 2 * n = n * 2 by omega, pow_mul]
    dsimp [c]
    rw [inv_pow, hpow]
    field_simp [ne_of_gt hε]
  have hexp : -((3 + 2 * n : ℕ) : ℝ) = -(3 + 2 * (n : ℝ)) := by
    push_cast
    rfl
  have hexpMulCast : -(3 + 2 * (n : ℝ)) =
      -(3 + ((2 * n : ℕ) : ℝ)) := by
    push_cast
    ring
  have hscaleSq :
      ∫ y : L2Vec3, ‖dε y‖ ^ 2 =
        ε ^ (-(3 + 2 * (n : ℝ))) * ∫ y : L2Vec3, ‖dρ y‖ ^ 2 := by
    calc
      ∫ y : L2Vec3, ‖dε y‖ ^ 2 =
          c ^ 2 * ∫ y : L2Vec3, ‖dρ (ε⁻¹ • y)‖ ^ 2 := by
            rw [show (fun y : L2Vec3 => ‖dε y‖ ^ 2) =
                fun y => c ^ 2 * ‖dρ (ε⁻¹ • y)‖ ^ 2 from by
                  funext y
                  rw [hpoint, norm_mul, Real.norm_eq_abs, abs_of_pos hcpos]
                  ring]
            rw [integral_const_mul]
      _ = c ^ 2 *
          (|ε ^ Module.finrank ℝ L2Vec3| * ∫ y : L2Vec3, ‖dρ y‖ ^ 2) := by
            rw [hchange]
      _ = ε ^ (-(3 + 2 * (n : ℝ))) *
          ∫ y : L2Vec3, ‖dρ y‖ ^ 2 := by
            rw [hdim, abs_of_pos (pow_pos hε 3)]
            rw [← mul_assoc, hcSq]
            rw [hexp]
  have hscaleReal :
      ∫ y : L2Vec3, ‖dε y‖ ^ (2 : ℝ) =
        ε ^ (-(3 + (2 * n : ℕ) : ℝ)) *
          ∫ y : L2Vec3, ‖dρ y‖ ^ (2 : ℝ) := by
    calc
      ∫ y : L2Vec3, ‖dε y‖ ^ (2 : ℝ) =
          ∫ y : L2Vec3, ‖dε y‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards [] with y
            exact Real.rpow_natCast _ 2
      _ = ε ^ (-(3 + (2 * n : ℕ) : ℝ)) *
          ∫ y : L2Vec3, ‖dρ y‖ ^ 2 := by
            rw [hscaleSq]
            exact congrArg (fun z : ℝ => ε ^ z *
              ∫ y : L2Vec3, ‖dρ y‖ ^ 2) hexpMulCast
      _ = ε ^ (-(3 + (2 * n : ℕ) : ℝ)) *
          ∫ y : L2Vec3, ‖dρ y‖ ^ (2 : ℝ) := by
            congr 2
            funext y
            exact (Real.rpow_natCast _ 2).symm
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hεmem,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hρmem]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  calc
    (∫ y : L2Vec3, ‖dε y‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ =
        (ε ^ (-(3 + (2 * n : ℕ) : ℝ)) *
          ∫ y : L2Vec3, ‖dρ y‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
            exact congrArg (fun z : ℝ => z ^ (2 : ℝ)⁻¹) hscaleReal
    _ = ε ^ (-(3 / 2 : ℝ) - (n : ℝ)) *
        (∫ y : L2Vec3, ‖dρ y‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            congr 1
            rw [← Real.rpow_mul (le_of_lt hε)]
            congr 1
            push_cast
            ring

end CKN.Leray

end
