/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierAllDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Weak-derivative identities for the regularized convolution

The convolution associated with `eq:reg-mollifier` commutes with scalar weak
spatial derivatives. Its vector-valued divergence constraint is preserved.
-/

public section

open MeasureTheory
open scoped ENNReal Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A smooth compactly supported convolution kernel commutes with a scalar
weak partial derivative on all of space. -/
theorem smoothCompactConvolution_spatialDeriv_eq_of_weak
    {κ f g : Vec3 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : LocallyIntegrable g volume) (j : Fin 3)
    (hweak : HasWeakPartialDerivOn (Set.univ : Set Vec3) j f g) (x : Vec3) :
    ConvolutionExists κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume ∧
    spatialDeriv
        (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) j x =
      MeasureTheory.convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  constructor
  · exact hκc.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ.continuous hg
  · let φ : Vec3 → ℝ := fun y => κ (x - y)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hκ.comp (contDiff_const.sub contDiff_id)
    have hφc : HasCompactSupport φ := by
      simpa [φ, Function.comp_def] using hκc.comp_homeomorph (Homeomorph.subLeft x)
    have hφderiv (y : Vec3) :
        (fderiv ℝ φ y) (basisVec j) = -(fderiv ℝ κ (x - y)) (basisVec j) := by
      have hinner : HasFDerivAt (fun z : Vec3 => x - z)
          (-(1 : Vec3 →L[ℝ] Vec3)) y := (hasFDerivAt_id y).const_sub x
      have houter : HasFDerivAt κ (fderiv ℝ κ (x - y)) (x - y) :=
        (hκ.differentiable (by simp) (x - y)).hasFDerivAt
      have hcomp := houter.comp y hinner
      simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
        congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hcomp.fderiv
    have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
    have hfd := hκc.hasFDerivAt_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (hκ.of_le (by norm_num)) hloc x
    have hderivConv : fderiv ℝ
        (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x =
        MeasureTheory.convolution (fderiv ℝ κ) f
          ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume x := by
      simpa using hfd.fderiv
    have hconvD : ConvolutionExists (fderiv ℝ κ) f
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3) volume := by
      exact HasCompactSupport.convolutionExists_left
        (𝕜 := ℝ) (G := Vec3) (E := Vec3 →L[ℝ] ℝ) (E' := ℝ)
        (F := Vec3 →L[ℝ] ℝ) ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3)
        (hκc.fderiv (𝕜 := ℝ))
        (hκ.continuous_fderiv (by norm_num)) hloc
    have hleft : spatialDeriv
        (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) j x =
        ∫ y : Vec3, (fderiv ℝ κ y) (basisVec j) * f (x - y) := by
      change (fderiv ℝ
        (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x)
          (basisVec j) = _
      rw [hderivConv, MeasureTheory.convolution,
        ContinuousLinearMap.integral_apply (hconvD x) (basisVec j)]
      simp [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul]
    have hweak' : (∫ y : Vec3, f y * (fderiv ℝ φ y) (basisVec j)) =
        -∫ y : Vec3, g y * φ y := by
      simpa [φ] using hweak φ hφ hφc (Set.subset_univ _)
    have hchange : (∫ y : Vec3,
        (fderiv ℝ κ y) (basisVec j) * f (x - y)) =
        ∫ y : Vec3, f y * (fderiv ℝ κ (x - y)) (basisVec j) := by
      calc
        _ = ∫ y : Vec3, f (x - y) * (fderiv ℝ κ y) (basisVec j) := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ = ∫ y : Vec3, f y * (fderiv ℝ κ (x - y)) (basisVec j) := by
          let F : Vec3 → ℝ := fun y => f y * (fderiv ℝ κ (x - y)) (basisVec j)
          simpa [F, sub_sub_cancel] using
            (Measure.measurePreserving_sub_left volume x).integral_comp
              (Homeomorph.subLeft x).measurableEmbedding F
    have hright : (∫ y : Vec3, κ y * g (x - y)) = ∫ y : Vec3, g y * φ y := by
      let F : Vec3 → ℝ := fun y => φ y * g y
      calc
        _ = ∫ y : Vec3, F (x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [F, φ]
        _ = ∫ y : Vec3, F y :=
          (Measure.measurePreserving_sub_left volume x).integral_comp
            (Homeomorph.subLeft x).measurableEmbedding F
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [F, mul_comm]
    rw [hleft]
    calc
      (∫ y : Vec3, (fderiv ℝ κ y) (basisVec j) * f (x - y)) =
          ∫ y : Vec3, f y * (fderiv ℝ κ (x - y)) (basisVec j) := hchange
      _ = -∫ y : Vec3, f y * (fderiv ℝ φ y) (basisVec j) := by
        rw [show (fun y : Vec3 => f y * (fderiv ℝ κ (x - y)) (basisVec j)) =
          fun y => -(f y * (fderiv ℝ φ y) (basisVec j) ) by
            funext y
            rw [hφderiv]
            ring]
        rw [integral_neg]
      _ = ∫ y : Vec3, g y * φ y := by rw [hweak']; simp
      _ = ∫ y : Vec3, κ y * g (x - y) := hright.symm

/-- The scalar kernel on the Euclidean coordinate carrier associated with
`regMollifierKernel`. -/
@[expose]
def regUniformMollifierKernel (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) : Vec3 → ℝ :=
  fun x => regMollifierKernel ρ ε hε (WithLp.toLp 2 x)

private theorem regUniformMollifierKernel_smooth
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regUniformMollifierKernel ρ ε hε) := by
  have hto : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => WithLp.toLp 2 x) := by fun_prop
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 x))
  exact contDiff_const.mul (ρ.smooth.comp ((contDiff_const_smul ε⁻¹).comp hto))

private theorem regUniformMollifierKernel_compact
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (regUniformMollifierKernel ρ ε hε) := by
  let hhomeo : Vec3 ≃ₜ L2Vec3 := CKN.Foundation.Parabolic.vec3Homeomorph
  let hscale : L2Vec3 ≃ₜ L2Vec3 := Homeomorph.smulOfNeZero ε⁻¹
    (inv_ne_zero (ne_of_gt hε))
  have hcomp := ρ.compact.comp_homeomorph (hhomeo.trans hscale)
  have hcompact : HasCompactSupport (fun x : Vec3 =>
      (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x)) := hcomp.mul_left
  have heq : regUniformMollifierKernel ρ ε hε = fun x : Vec3 =>
      (ε ^ 3)⁻¹ * ρ.rho ((hhomeo.trans hscale) x) := by
    funext x
    simp [regUniformMollifierKernel, regMollifierKernel, hhomeo, hscale,
      Homeomorph.trans_apply]
  rw [heq]
  exact hcompact

/-- The tuple of coordinate directions associated with an ordered derivative. -/
@[expose]
def regUniformMollifierCoordinateTuple (n : ℕ)
    (w : Fin n → Fin 3) : Fin n → Vec3 :=
  fun k => basisVec (w k)

private theorem regUniformMollifierKernel_coordinateDerivative_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (w : Fin n → Fin 3) :
    MemLp (fun y : Vec3 =>
      (iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε) y)
        (regUniformMollifierCoordinateTuple n w))
      (2 : ℝ≥0∞) volume := by
  let d : Vec3 → ℝ := fun y =>
    (iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε) y)
      (regUniformMollifierCoordinateTuple n w)
  have hcont : Continuous d := by
    dsimp [d]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec3) ℝ
      (regUniformMollifierCoordinateTuple n w)).continuous.comp
        ((regUniformMollifierKernel_smooth ρ ε hε).continuous_iteratedFDeriv
          (by simp))
  have hcompact : HasCompactSupport d := by
    have hiter : HasCompactSupport
        (iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε) :
          Vec3 → ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) ℝ) :=
      (regUniformMollifierKernel_compact ρ ε hε).iteratedFDeriv n
    apply HasCompactSupport.of_support_subset_isCompact hiter.isCompact
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hnot
    have hzero : iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε) y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε)) hnot
    exact hy (by simp [d, hzero])
  exact hcont.memLp_of_hasCompactSupport hcompact

private theorem regMollifierAssemblyKernel_smoothOnL2
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regMollifierKernel ρ ε hε) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun y : L2Vec3 => ε⁻¹ • y) := by fun_prop
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun y : L2Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
  exact contDiff_const.mul (ρ.smooth.comp hscale)

private theorem regMollifierAssemblyVectorConvolution_iterated
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (v : Fin n → L2Vec3)
    {f : L2Vec3 → L2Vec3} (hf : LocallyIntegrable f volume) (x : L2Vec3) :
    (iteratedFDeriv ℝ n
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume) x) v =
      ∫ y : L2Vec3,
        (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v • f (x - y) := by
  let k : L2Vec3 → ℝ := regMollifierKernel ρ ε hε
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := by
    simpa [k] using regMollifierAssemblyKernel_smoothOnL2 ρ ε hε
  have hkc : HasCompactSupport k := by
    dsimp [k, regMollifierKernel]
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have h := ρ.compact.comp_homeomorph (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    change HasCompactSupport (fun y => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact h.mul_left
  induction n generalizing x with
  | zero =>
      change (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) x = _
      rfl
  | succ n ih =>
      let ktail : L2Vec3 → ℝ := fun y =>
        (iteratedFDeriv ℝ n k y) (Fin.tail v)
      have htailSmooth : ContDiff ℝ 2 ktail := by
        have hIter : ContDiff ℝ 2 (iteratedFDeriv ℝ n k) := by
          have hNat : ContDiff ℝ (2 + n) k := hk.of_le (by simp)
          exact hNat.iteratedFDeriv_right' (m := 2) (i := n)
        change ContDiff ℝ 2 (fun y =>
          (iteratedFDeriv ℝ n k y) (Fin.tail v))
        exact hIter.continuousLinearMap_comp (ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin n => L2Vec3) ℝ (Fin.tail v))
      have htailCompact : HasCompactSupport ktail := by
        have hIter : HasCompactSupport (iteratedFDeriv ℝ n k) := hkc.iteratedFDeriv n
        apply HasCompactSupport.of_support_subset_isCompact hIter.isCompact
        intro y hy
        simp only [Function.mem_support] at hy
        by_contra hnot
        have hz : iteratedFDeriv ℝ n k y = 0 :=
          image_eq_zero_of_notMem_tsupport (f := iteratedFDeriv ℝ n k) hnot
        exact hy (by simp [ktail, hz])
      have hIHfun : (fun z : L2Vec3 =>
          (iteratedFDeriv ℝ n
            (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) z)
              (Fin.tail v)) =
          MeasureTheory.convolution ktail f allDerivativeScalarVectorAction volume := by
        funext z
        have h := ih (Fin.tail v) z
        simpa [MeasureTheory.convolution, ktail,
          allDerivativeScalarVectorAction,
          allDerivativeScalarVectorActionLinear] using h
      have hconvD := allDerivativeScalarVectorConvolution_directional_deriv
        ktail htailSmooth htailCompact hf x (v 0)
      have hconvSmooth : ContDiff ℝ (⊤ : ℕ∞)
          (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume) :=
        hkc.contDiff_convolution_left (n := ⊤)
          (L := allDerivativeScalarVectorAction) hk hf
      have hconvDiff : DifferentiableAt ℝ
          (iteratedFDeriv ℝ n
            (MeasureTheory.convolution k f allDerivativeScalarVectorAction volume)) x :=
        hconvSmooth.contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top n)
      rw [hconvDiff.iteratedFDeriv_succ_apply_left' (m := v)]
      rw [hIHfun]
      change (fderiv ℝ (MeasureTheory.convolution ktail f
        allDerivativeScalarVectorAction volume) x) (v 0) = _
      rw [hconvD]
      apply integral_congr_ae
      filter_upwards [] with y
      have hderiv : (fderiv ℝ ktail y) (v 0) =
          (iteratedFDeriv ℝ (n + 1) k y) v := by
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n k) y :=
          hk.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast ENat.natCast_lt_top n)
        symm
        simpa [ktail] using hdiff.iteratedFDeriv_succ_apply_left' (m := v)
      rw [hderiv]

/-- Every ordered derivative of vector mollification is bounded by the
corresponding derivative-kernel norm times the input's `L²` norm. -/
theorem regMollifyVector_iteratedDerivative_enorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume)
    (n : ℕ) (v : Fin n → L2Vec3) (x : L2Vec3) :
    ‖(iteratedFDeriv ℝ n (regMollifyVector ρ ε hε f) x) v‖ₑ ≤
      eLpNorm (fun y : L2Vec3 =>
        (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v) 2 volume *
        eLpNorm f 2 volume := by
  let dk : L2Vec3 → ℝ := fun y =>
    (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v
  have hdkContinuous : Continuous dk := by
    dsimp [dk]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => L2Vec3) ℝ v).continuous.comp
      ((regMollifierAssemblyKernel_smoothOnL2 ρ ε hε).continuous_iteratedFDeriv (by simp))
  have hkernelCompact : HasCompactSupport (regMollifierKernel ρ ε hε) := by
    unfold regMollifierKernel
    have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
    have hcompact := ρ.compact.comp_homeomorph
      (Homeomorph.smulOfNeZero ε⁻¹ hscaleNe)
    change HasCompactSupport (fun y => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • y))
    exact hcompact.mul_left
  have hdkCompact : HasCompactSupport dk := by
    have hIter : HasCompactSupport (iteratedFDeriv ℝ n
        (regMollifierKernel ρ ε hε) :
          L2Vec3 → ContinuousMultilinearMap ℝ (fun _ : Fin n => L2Vec3) ℝ) :=
      hkernelCompact.iteratedFDeriv n
    apply HasCompactSupport.of_support_subset_isCompact hIter.isCompact
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hnot
    have hz : iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε)) hnot
    exact hy (by simp [dk, hz])
  have hdk : MemLp dk (2 : ℝ≥0∞) volume :=
    hdkContinuous.memLp_of_hasCompactSupport hdkCompact
  have hformula : (iteratedFDeriv ℝ n
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume) x) v =
      MeasureTheory.convolution dk f allDerivativeScalarVectorAction volume x := by
    rw [MeasureTheory.convolution]
    rw [regMollifierAssemblyVectorConvolution_iterated ρ ε hε n v
      (hf.locallyIntegrable (by norm_num)) x]
    rfl
  have hconv := MeasureTheory.enorm_convolution_le
    (L := allDerivativeScalarVectorAction) (p := (2 : ℝ≥0∞)) (q := 2)
    hdk.aestronglyMeasurable hf.aestronglyMeasurable x
  have hL : ‖allDerivativeScalarVectorAction‖ₑ ≤ 1 := by
    apply ContinuousLinearMap.opENorm_le_iff.mpr
    intro c
    have hc : ‖allDerivativeScalarVectorAction c‖ₑ ≤ ‖c‖ₑ := by
      apply ContinuousLinearMap.opENorm_le_bound
      intro z
      change ‖c • z‖ₑ ≤ _
      exact enorm_smul_le
    calc
      ‖allDerivativeScalarVectorAction c‖ₑ ≤ ‖c‖ₑ := hc
      _ = 1 * ‖c‖ₑ := by simp
  change ‖(iteratedFDeriv ℝ n
      (MeasureTheory.convolution (regMollifierKernel ρ ε hε) f
        allDerivativeScalarVectorAction volume) x) v‖ₑ ≤ _
  rw [hformula]
  calc
    ‖MeasureTheory.convolution dk f allDerivativeScalarVectorAction volume x‖ₑ ≤
      ‖allDerivativeScalarVectorAction‖ₑ * eLpNorm dk 2 volume * eLpNorm f 2 volume := hconv
    _ ≤ eLpNorm dk 2 volume * eLpNorm f 2 volume := by
      calc
        _ = (‖allDerivativeScalarVectorAction‖ₑ * eLpNorm dk 2 volume) *
            eLpNorm f 2 volume := by ring
        _ ≤ (1 * eLpNorm dk 2 volume) * eLpNorm f 2 volume :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hL (by positivity)) (by positivity)
        _ = eLpNorm dk 2 volume * eLpNorm f 2 volume := by simp [dk]

/-- The all-orders smoothing estimate and spatial `L²` contraction for the
regularizing operator. -/
theorem regMollifierLemmaAssembly_bounds
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : L2Vec3 → L2Vec3} (hf : MemLp f (2 : ℝ≥0∞) volume)
    (n : ℕ) (v : Fin n → L2Vec3) (x : L2Vec3) :
    (eLpNorm (regMollifyVector ρ ε hε f) 2 volume ≤ eLpNorm f 2 volume) ∧
      (‖(iteratedFDeriv ℝ n (regMollifyVector ρ ε hε f) x) v‖ₑ ≤
        ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ) - (n : ℝ))) *
          eLpNorm (fun y : L2Vec3 => (iteratedFDeriv ℝ n ρ.rho y) v) 2 volume *
          eLpNorm f 2 volume) := by
  constructor
  · exact regMollifyVector_eLpNorm_two_le ρ ε hε hf
  · calc
      _ ≤ eLpNorm (fun y : L2Vec3 =>
            (iteratedFDeriv ℝ n (regMollifierKernel ρ ε hε) y) v) 2 volume *
          eLpNorm f 2 volume :=
        regMollifyVector_iteratedDerivative_enorm_le ρ ε hε hf n v x
      _ = ENNReal.ofReal (ε ^ (-(3 / 2 : ℝ) - (n : ℝ))) *
          eLpNorm (fun y : L2Vec3 => (iteratedFDeriv ℝ n ρ.rho y) v) 2 volume *
          eLpNorm f 2 volume := by
        rw [regMollifierKernel_iteratedDerivative_eLpNorm_two ρ ε hε n v]

/-- Every ordered coordinate derivative of a mollified component is bounded
pointwise by the `L²` norm of the corresponding differentiated kernel times
the `L²` norm of the input component. -/
theorem regUniformMollifiedInitial_coordinateDerivative_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (n : ℕ) (w : Fin n → Fin 3) (i : Fin 3) (x : Vec3) :
    ‖(iteratedFDeriv ℝ n
      (fun y => regUniformMollifiedInitial ρ ε hε a y i) x)
        (regUniformMollifierCoordinateTuple n w)‖ₑ ≤
      eLpNorm (fun y : Vec3 =>
        (iteratedFDeriv ℝ n (regUniformMollifierKernel ρ ε hε) y)
          (regUniformMollifierCoordinateTuple n w)) 2 volume *
        eLpNorm (fun y : Vec3 => a y i) 2 volume := by
  let κ := regUniformMollifierKernel ρ ε hε
  let f : Vec3 → ℝ := fun y => a y i
  let dk : Vec3 → ℝ := fun y =>
    (iteratedFDeriv ℝ n κ y) (regUniformMollifierCoordinateTuple n w)
  have hf : MemLp f (2 : ℝ≥0∞) volume := ha.eval i
  have hcomponent : (fun y : Vec3 => regUniformMollifiedInitial ρ ε hε a y i) =
      MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y
    exact regUniformMollifiedInitial_component_convolution ρ ε hε ha y i
  have hformula := regularisedScalarConvolution_iterated_derivative
    n w κ (regUniformMollifierKernel_smooth ρ ε hε)
    (regUniformMollifierKernel_compact ρ ε hε) hf x
  have hvalue :
      (iteratedFDeriv ℝ n
        (fun y => regUniformMollifiedInitial ρ ε hε a y i) x)
          (regUniformMollifierCoordinateTuple n w) =
        MeasureTheory.convolution dk f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [hcomponent]
    change (iteratedFDeriv ℝ n
      (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x)
        (fun k => basisVec (w k)) =
      MeasureTheory.convolution
        (fun y => (iteratedFDeriv ℝ n κ y) (fun k => basisVec (w k))) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    exact hformula
  have hk : MemLp dk (2 : ℝ≥0∞) volume := by
    simpa [dk, κ] using
      regUniformMollifierKernel_coordinateDerivative_memLp ρ ε hε n w
  have hconv := MeasureTheory.enorm_convolution_le
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (p := (2 : ℝ≥0∞)) (q := 2)
    hk.aestronglyMeasurable hf.aestronglyMeasurable x
  have hL : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ ≤ 1 := by
    apply ContinuousLinearMap.opENorm_le_iff.mpr
    intro c
    have hc : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) c‖ₑ ≤ ‖c‖ₑ := by
      apply ContinuousLinearMap.opENorm_le_bound
      intro z
      change ‖c • z‖ₑ ≤ _
      exact enorm_smul_le
    calc
      ‖ContinuousLinearMap.lsmul ℝ ℝ c‖ₑ ≤ ‖c‖ₑ := hc
      _ = 1 * ‖c‖ₑ := by simp
  rw [hvalue]
  calc
    ‖MeasureTheory.convolution dk f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤
      ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ *
        eLpNorm dk 2 volume * eLpNorm f 2 volume := hconv
    _ ≤ eLpNorm dk 2 volume * eLpNorm f 2 volume := by
      calc
        _ = (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ *
            eLpNorm dk 2 volume) * eLpNorm f 2 volume := by ring
        _ ≤ (1 * eLpNorm dk 2 volume) * eLpNorm f 2 volume :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hL (by positivity)) (by positivity)
        _ = _ := by simp [dk, κ]

/-- Classical derivatives of the mollified vector field equal the mollified
function-valued weak derivatives coordinate by coordinate. -/
theorem regUniformMollifiedInitial_spatialDeriv_eq_weak
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (g : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hg : ∀ i j, LocallyIntegrable (g i j) volume)
    (hweak : ∀ i j, HasWeakPartialDerivOn (Set.univ : Set Vec3) j
      (fun x => a x i) (g i j)) (x : Vec3) (i j : Fin 3) :
    spatialDeriv (fun y => regUniformMollifiedInitial ρ ε hε a y i) j x =
      MeasureTheory.convolution (regUniformMollifierKernel ρ ε hε)
        (g i j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hcomponent := regUniformMollifiedInitial_component_convolution ρ ε hε ha x i
  have hf : MemLp (fun y : Vec3 => a y i) (2 : ℝ≥0∞) volume := ha.eval i
  rw [funext (fun y => regUniformMollifiedInitial_component_convolution ρ ε hε ha y i)]
  exact (smoothCompactConvolution_spatialDeriv_eq_of_weak
    (regUniformMollifierKernel_smooth ρ ε hε)
    (regUniformMollifierKernel_compact ρ ε hε) hf (hg i j) j (hweak i j) x).2

/-- The regularized initial field remains in the Leray space; in particular,
its weak divergence is zero. -/
theorem regMollifierLemmaAssembly_preserves_divergence
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsWeakDivFreeL2 a) :
    CKN.IsWeakDivFreeL2 (regUniformMollifiedInitial ρ ε hε a) :=
  CKN.isInJ_weakDivFree
    (regMollifiedInitial_isInJ ρ ε hε (CKN.weakDivFreeL2_isInJ ha))

end CKN.Leray

end
