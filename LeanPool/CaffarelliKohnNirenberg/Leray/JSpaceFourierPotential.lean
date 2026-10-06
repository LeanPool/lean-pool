/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.VectorPotential
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourier
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierPotentialBase

/-!
# Fourier identities for the regularized Leray potential
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal FourierTransform LineDeriv SchwartzMap
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN



private theorem weakDivFreeL2_l2Schwartz {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (ψ : SchwartzMap L2Vec3 ℝ) :
    ∫ x : L2Vec3, ∑ i : Fin 3,
      a (l2Vec3Equiv x) i * l2SpatialDeriv ψ i x = 0 := by
  let ψV : 𝓢(Vec3, ℝ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ l2Vec3Equiv.symm ψ
  have hweak := isWeakDivFreeL2_schwartz ha ψV
  have hderiv (i : Fin 3) (y : Vec3) :
      spatialDeriv (fun z : Vec3 => ψV z) i y =
        l2SpatialDeriv ψ i (l2Vec3Equiv.symm y) := by
    change (∂_{basisVec i} ψV) y =
      (∂_{l2Vec3Equiv.symm (basisVec i)} ψ) (l2Vec3Equiv.symm y)
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv
      ℝ (basisVec i) l2Vec3Equiv.symm ψ]
    rfl
  let F : L2Vec3 → ℝ := fun x => ∑ i : Fin 3,
    a (l2Vec3Equiv x) i * l2SpatialDeriv ψ i x
  have htransport : MeasurePreserving (l2Vec3Equiv.symm : Vec3 → L2Vec3)
      volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hembedding : MeasurableEmbedding (l2Vec3Equiv.symm : Vec3 → L2Vec3) :=
    l2Vec3Equiv.symm.toHomeomorph.measurableEmbedding
  have hchange (y : Vec3) : F (l2Vec3Equiv.symm y) =
      ∑ i : Fin 3, a y i * spatialDeriv ψV i y := by
    simp [F, hderiv]
  calc
    ∫ x : L2Vec3, F x = ∫ y : Vec3, F (l2Vec3Equiv.symm y) :=
      (htransport.integral_comp hembedding F).symm
    _ = ∫ y : Vec3, ∑ i : Fin 3, a y i * spatialDeriv ψV i y := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hchange y
    _ = 0 := hweak

private theorem weakDivFreeL2_l2ComplexSchwartz {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (ψ : SchwartzMap L2Vec3 ℂ) :
    ∫ x : L2Vec3, ∑ i : Fin 3,
      weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x = 0 := by
  let ψre := ψ.postcompCLM Complex.reCLM
  let ψim := ψ.postcompCLM Complex.imCLM
  have hderivRe (i : Fin 3) (x : L2Vec3) :
      l2SpatialDeriv ψre i x = Complex.re ((∂_{l2BasisVec3 i} ψ) x) := by
    change (∂_{l2BasisVec3 i} ψre) x = _
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ (fun y => Complex.re (ψ y)) x) (l2BasisVec3 i) = _
    have hψ : DifferentiableAt ℝ (ψ : L2Vec3 → ℂ) x :=
      (ψ.smooth ⊤).differentiable (by simp) x
    have hcomp := fderiv_comp (𝕜 := ℝ) (f := fun y : L2Vec3 => ψ y)
      (g := fun z : ℂ => Complex.re z) (x := x) (by fun_prop) hψ
    rw [show (fun y : L2Vec3 => Complex.re (ψ y)) =
      (fun z : ℂ => Complex.re z) ∘ ψ from rfl, hcomp]
    have hlin : fderiv ℝ (fun z : ℂ => Complex.re z) (ψ x) = Complex.reCLM :=
      Complex.reCLM.hasFDerivAt.fderiv
    rw [hlin]
    rfl
  have hderivIm (i : Fin 3) (x : L2Vec3) :
      l2SpatialDeriv ψim i x = Complex.im ((∂_{l2BasisVec3 i} ψ) x) := by
    change (∂_{l2BasisVec3 i} ψim) x = _
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ (fun y => Complex.im (ψ y)) x) (l2BasisVec3 i) = _
    have hψ : DifferentiableAt ℝ (ψ : L2Vec3 → ℂ) x :=
      (ψ.smooth ⊤).differentiable (by simp) x
    have hcomp := fderiv_comp (𝕜 := ℝ) (f := fun y : L2Vec3 => ψ y)
      (g := fun z : ℂ => Complex.im z) (x := x) (by fun_prop) hψ
    rw [show (fun y : L2Vec3 => Complex.im (ψ y)) =
      (fun z : ℂ => Complex.im z) ∘ ψ from rfl, hcomp]
    have hlin : fderiv ℝ (fun z : ℂ => Complex.im z) (ψ x) = Complex.imCLM :=
      Complex.imCLM.hasFDerivAt.fderiv
    rw [hlin]
    rfl
  have hfield (i : Fin 3) : ∀ᵐ x : L2Vec3 ∂volume,
      weakFieldFourierComponent ha.1 i x = (a (WithLp.ofLp x) i : ℂ) := by
    filter_upwards [(complexifyVec3_memLp ha.1).eval_piLp i |>.coeFn_toLp] with x hx
    simpa [weakFieldFourierComponent, complexifyVec3] using hx
  have hterm (i : Fin 3) :
      Integrable (fun x : L2Vec3 =>
        weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) volume :=
    (Lp.memLp (weakFieldFourierComponent ha.1 i)).integrable_mul
      ((∂_{l2BasisVec3 i} ψ).memLp (2 : ℝ≥0∞) volume)
  have hsum : Integrable (fun x : L2Vec3 => ∑ i : Fin 3,
      weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) volume := by
    exact integrable_finsetSum (s := Finset.univ) (fun i hi => hterm i)
  have hweakRe := weakDivFreeL2_l2Schwartz ha ψre
  have hweakIm := weakDivFreeL2_l2Schwartz ha ψim
  have hReIntegral : Complex.re (∫ x : L2Vec3, ∑ i : Fin 3,
      weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) =
      ∫ x : L2Vec3, Complex.re (∑ i : Fin 3,
        weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) :=
    (integral_re hsum).symm
  have hImIntegral : Complex.im (∫ x : L2Vec3, ∑ i : Fin 3,
      weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) =
      ∫ x : L2Vec3, Complex.im (∑ i : Fin 3,
        weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) :=
    (integral_im hsum).symm
  apply Complex.ext
  · rw [hReIntegral]
    have hReEq :
        (∫ x : L2Vec3, Complex.re (∑ i : Fin 3,
          weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x)) =
        ∫ x : L2Vec3, ∑ i : Fin 3, a (l2Vec3Equiv x) i * l2SpatialDeriv ψre i x := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hfield] with x hx
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, ← hderivRe i x]
      rfl
    exact hReEq.trans hweakRe
  · rw [hImIntegral]
    have hImEq :
        (∫ x : L2Vec3, Complex.im (∑ i : Fin 3,
          weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x)) =
        ∫ x : L2Vec3, ∑ i : Fin 3, a (l2Vec3Equiv x) i * l2SpatialDeriv ψim i x := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hfield] with x hx
      simp only [Complex.im_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, ← hderivIm i x]
      rfl
    exact hImEq.trans hweakIm

private theorem weakDivFreeL2_distributionDivergence_zero {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) :
    ∑ i : Fin 3, ∂_{l2BasisVec3 i}
      (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) = 0 := by
  ext ψ
  have hweak := weakDivFreeL2_l2ComplexSchwartz ha ψ
  have hpart (i : Fin 3) : Integrable (fun x : L2Vec3 =>
      weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) volume :=
    (Lp.memLp (weakFieldFourierComponent ha.1 i)).integrable_mul
      ((∂_{l2BasisVec3 i} ψ).memLp (2 : ℝ≥0∞) volume)
  have heval (i : Fin 3) :
      (∂_{l2BasisVec3 i}
        (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ))) ψ =
        -(∫ x : L2Vec3,
          weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x) := by
    simp only [TemperedDistribution.lineDerivOp_apply_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply, smul_eq_mul]
    rw [show (fun x : L2Vec3 => (-∂_{l2BasisVec3 i} ψ) x *
        weakFieldFourierComponent ha.1 i x) =
        fun x => -(weakFieldFourierComponent ha.1 i x *
          (∂_{l2BasisVec3 i} ψ) x) by
      funext x
      change (-((∂_{l2BasisVec3 i} ψ) x)) *
        weakFieldFourierComponent ha.1 i x = _
      ring]
    exact integral_neg _
  have hsumInt :
      ∫ x : L2Vec3, ∑ i : Fin 3,
        weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x ∂volume =
      ∑ i : Fin 3, ∫ x : L2Vec3,
        weakFieldFourierComponent ha.1 i x * (∂_{l2BasisVec3 i} ψ) x ∂volume := by
    exact integral_finsetSum (s := Finset.univ) (fun i hi => hpart i)
  change (∑ i : Fin 3,
    (∂_{l2BasisVec3 i} (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ))) ψ) = 0
  rw [Finset.sum_congr rfl (fun i hi => heval i)]
  rw [Finset.sum_neg_distrib, ← hsumInt, hweak, neg_zero]

private theorem weakDivFreeL2_frequencyMultiplierDivergence_zero {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) :
    ∑ i : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord i ξ))
      (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) = 0 := by
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hline (i : Fin 3) :
      ∂_{l2BasisVec3 i}
        (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) =
      c • TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord i ξ))
        (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) := by
    rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM]
    congr 2
    congr 1
    funext ξ
    simp [inner_l2BasisVec3]
  have hsum : ∑ i : Fin 3, c • TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord i ξ))
      (weakFieldFourierComponent ha.1 i : 𝓢'(L2Vec3, ℂ)) = 0 := by
    simpa only [hline] using weakDivFreeL2_distributionDivergence_zero ha
  rw [← Finset.smul_sum] at hsum
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      Complex.I_ne_zero
  exact (smul_eq_zero.mp hsum).resolve_left hc

/-- The regularization weight times its quadratic denominator is one. -/
theorem regularizedFrequencyWeight_mul_one_add_sum_sq
    (δ : ℝ) (ξ : L2Vec3) :
    regularizedFrequencyWeight δ ξ *
      (1 + ∑ i : Fin 3, (regularizedFrequencyCoord δ i ξ) ^ 2) = 1 := by
  let η : L2Vec3 := (δ⁻¹ : ℝ) • ξ
  have hsum : ∑ i : Fin 3, (regularizedFrequencyCoord δ i ξ) ^ 2 = ‖η‖ ^ 2 := by
    calc
      ∑ i : Fin 3, (regularizedFrequencyCoord δ i ξ) ^ 2 =
          ∑ i : Fin 3, (frequencyL2Coord i η) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [regularizedFrequencyCoord_eq_scaled]
      _ = ‖η‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        apply Finset.sum_congr rfl
        intro i hi
        simp [frequencyL2Coord, PiLp.proj_apply, Real.norm_eq_abs, sq_abs]
  have hweight : regularizedFrequencyWeight δ ξ =
      1 / (1 + ‖η‖ ^ 2) := by
    rw [regularizedFrequencyWeight, Real.rpow_neg (by positivity)]
    simp [η, Real.rpow_one]
  rw [hweight, hsum]
  field_simp

private theorem regularizedPotentialVec3_memLp {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (regularizedPotentialVec3 ha δ hδ) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  let potential := regularizedPotentialComponentLp ha δ hδ i
  have hreal : MemLp (fun x : L2Vec3 => Complex.re (potential x))
      (2 : ℝ≥0∞) volume := by
    exact (Lp.memLp potential).continuousLinearMap_comp Complex.reCLM
  have htransport : MeasurePreserving (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have h := hreal.comp_measurePreserving htransport
  simpa [regularizedPotentialVec3, regularizedPotentialComponentLp, potential,
    Function.comp_def] using h

private theorem regularizedPotentialGradientVec3_memLp {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (regularizedPotentialGradientVec3 ha δ hδ) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro k
  let derivative := regularizedPotentialDerivativeComponentLp ha δ hδ i k
  have hreal : MemLp (fun x : L2Vec3 => Complex.re (derivative x))
      (2 : ℝ≥0∞) volume := by
    exact (Lp.memLp derivative).continuousLinearMap_comp Complex.reCLM
  have htransport : MeasurePreserving (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have h := hreal.comp_measurePreserving htransport
  simpa [regularizedPotentialGradientVec3, regularizedPotentialDerivativeComponentLp,
    weakFieldFourierComponent, derivative, Function.comp_def] using h

/-- The curl of the regularized potential field. -/
@[expose]
def regularizedPotentialCurl {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) : Vec3 → Vec3 :=
  curlOfGradient (regularizedPotentialGradientVec3 ha δ hδ)

/-- Each regularized potential curl belongs to the `L²` closure defining `J`. -/
theorem regularizedPotentialCurl_memJ {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) :
    IsInJ (regularizedPotentialCurl ha δ hδ) := by
  let A := regularizedPotentialVec3 ha δ hδ
  let G := regularizedPotentialGradientVec3 ha δ hδ
  have hA : MemLp A (2 : ℝ≥0∞) volume := regularizedPotentialVec3_memLp ha δ hδ
  have hG : MemLp G (2 : ℝ≥0∞) volume := regularizedPotentialGradientVec3_memLp ha δ hδ
  have hcurl : MemLp (curlOfGradient G) (2 : ℝ≥0∞) volume := by
    apply curlOfGradient_memLp
    intro i k
    exact (hG.eval i).eval k
  have hweak (i k : Fin 3) :
      CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) k
        (fun x => A x i) (fun x => G x i k) := by
    exact regularizedPotentialVec3_hasWeakPartialDerivOn ha δ hδ i k
      (regularizedPotentialComponentLp_is_weakDeriv ha δ hδ i k)
  let ε : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  let Aseq : ℕ → Vec3 → Vec3 := fun n => spatialMollifyVec3 A (ε n) (hεpos n)
  have hAseqSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Aseq n) :=
    spatialMollifyVec3_contDiff (hεpos n) hA
  have hAseqLp (n : ℕ) : MemLp (Aseq n) (2 : ℝ≥0∞) volume :=
    spatialMollifyVec3_memLp (hεpos n) hA
  have hcurlEq (n : ℕ) :
      curlVec3 (Aseq n) = spatialMollifyVec3 (curlOfGradient G) (ε n) (hεpos n) := by
    funext x
    exact curl_spatialMollify_eq_spatialMollify_curlOfGradient hA hG hweak
      (hεpos n) x
  have hcurlLp (n : ℕ) : MemLp (curlVec3 (Aseq n)) (2 : ℝ≥0∞) volume := by
    rw [hcurlEq n]
    exact spatialMollifyVec3_memLp (hεpos n) hcurl
  have hJ (n : ℕ) : IsInJ (curlVec3 (Aseq n)) :=
    smoothL2Potential_curl_memJ (hAseqSmooth n) (hAseqLp n) (hcurlLp n)
  have hlim := spatialMollifyVec3_tendsto_L2 hcurl
  have hlim' : Tendsto
      (fun n : ℕ => eLpNorm (curlVec3 (Aseq n) - curlOfGradient G)
        (2 : ℝ≥0∞) volume) atTop (nhds 0) := by
    simpa [Aseq, ε, hcurlEq] using hlim
  have hJlimit : IsInJ (curlOfGradient G) :=
    isInJ_closed_under_L2_limit hcurl hJ hlim'
  simpa [regularizedPotentialCurl, G] using hJlimit

/-- One complex coordinate of the regularized curl. -/
@[expose]
def regularizedPotentialCurlComponentLp {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) :
    Lp (α := L2Vec3) ℂ 2 :=
  if i = 0 then
    regularizedPotentialDerivativeComponentLp ha δ hδ 2 1 -
      regularizedPotentialDerivativeComponentLp ha δ hδ 1 2
  else if i = 1 then
    regularizedPotentialDerivativeComponentLp ha δ hδ 0 2 -
      regularizedPotentialDerivativeComponentLp ha δ hδ 2 0
  else
    regularizedPotentialDerivativeComponentLp ha δ hδ 1 0 -
      regularizedPotentialDerivativeComponentLp ha δ hδ 0 1

/-- The `L²` embedding into tempered distributions preserves subtraction. -/
theorem toTemperedDistribution_sub_l2
    (u v : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
    ((u - v : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
      𝓢'(L2Vec3, ℂ)) = (u : 𝓢'(L2Vec3, ℂ)) - (v : 𝓢'(L2Vec3, ℂ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let T := MeasureTheory.Lp.toTemperedDistributionCLM (E := L2Vec3) ℂ volume 2
  simpa [T] using
    (MeasureTheory.Lp.toTemperedDistributionCLM (E := L2Vec3) ℂ volume 2).map_sub u v

/-- The distribution associated to a regularized curl coordinate is the
corresponding combination of first-derivative Fourier multipliers. -/
theorem regularizedPotentialCurlComponentLp_toDist
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) :
    ((regularizedPotentialCurlComponentLp ha δ hδ i :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      if i = 0 then
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 0)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 1)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ))) -
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 2)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 0)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)))
      else if i = 1 then
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 1)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 2 2)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ))) -
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 0)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 1)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)))
      else
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 2)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 0 0)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ))) -
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 1)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ 1 2)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ))) := by
  fin_cases i
  · simp only [regularizedPotentialCurlComponentLp, Fin.zero_eta, Fin.isValue,
      ↓reduceIte]
    rw [toTemperedDistribution_sub_l2,
      regularizedPotentialDerivativeComponentLp_toDist_two,
      regularizedPotentialDerivativeComponentLp_toDist_one]
  · simp only [regularizedPotentialCurlComponentLp, Fin.mk_one, Fin.isValue,
      one_ne_zero, ↓reduceIte]
    rw [toTemperedDistribution_sub_l2,
      regularizedPotentialDerivativeComponentLp_toDist_two,
      regularizedPotentialDerivativeComponentLp_toDist_zero]
  · simp only [regularizedPotentialCurlComponentLp, Fin.reduceFinMk, Fin.isValue,
      Fin.reduceEq, ↓reduceIte]
    rw [toTemperedDistribution_sub_l2,
      regularizedPotentialDerivativeComponentLp_toDist_zero,
      regularizedPotentialDerivativeComponentLp_toDist_one]

/-- The complex-valued Fourier coordinate functional for component `i`. -/
@[expose]
def frequencyCoordinateComplex (i : Fin 3) : L2Vec3 → ℂ :=
  fun ξ => Complex.ofReal (frequencyL2Coord i ξ)

/-- The complex Fourier weight obtained from the real regularized frequency weight. -/
@[expose]
def regularizedWeightComplex (δ : ℝ) : L2Vec3 → ℂ :=
  fun ξ => Complex.ofReal (regularizedFrequencyWeight δ ξ)

/-- The `i`th frequency coordinate multiplied by the regularized Fourier weight. -/
@[expose]
def weightedFrequencyCoordinate (δ : ℝ) (i : Fin 3) : L2Vec3 → ℂ :=
  fun ξ => frequencyCoordinateComplex i ξ * regularizedWeightComplex δ ξ

private theorem frequencyCoordinateComplex_hasTemperateGrowth (i : Fin 3) :
    (frequencyCoordinateComplex i).HasTemperateGrowth := by
  change (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord i ξ)).HasTemperateGrowth
  exact Complex.hasTemperateGrowth_ofReal.comp
    (_root_.ContinuousLinearMap.hasTemperateGrowth (frequencyL2Coord i))

private theorem regularizedWeightComplex_hasTemperateGrowth (δ : ℝ) :
    (regularizedWeightComplex δ).HasTemperateGrowth := by
  change (fun ξ : L2Vec3 => Complex.ofReal (regularizedFrequencyWeight δ ξ)).HasTemperateGrowth
  exact Complex.hasTemperateGrowth_ofReal.comp (regularizedFrequencyWeight_hasTemperateGrowth δ)

private theorem weightedFrequencyCoordinate_hasTemperateGrowth (δ : ℝ) (i : Fin 3) :
    (weightedFrequencyCoordinate δ i).HasTemperateGrowth := by
  change (frequencyCoordinateComplex i * regularizedWeightComplex δ).HasTemperateGrowth
  exact (frequencyCoordinateComplex_hasTemperateGrowth i).mul
    (regularizedWeightComplex_hasTemperateGrowth δ)

private theorem weakDivFreeL2_weightedFrequencyDivergence_zero {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (δ : ℝ) (i : Fin 3) :
    ∑ j : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ
      (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i)
      (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) = 0 := by
  let m := weightedFrequencyCoordinate δ i
  have hmul := congrArg (TemperedDistribution.fourierMultiplierCLM ℂ m)
    (weakDivFreeL2_frequencyMultiplierDivergence_zero ha)
  rw [map_sum] at hmul
  have hterms : ∑ j : Fin 3,
      TemperedDistribution.fourierMultiplierCLM ℂ m
        (TemperedDistribution.fourierMultiplierCLM ℂ
          (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord j ξ))
          (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ))) =
      ∑ j : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ
        ((fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord j ξ)) * m)
        (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (frequencyCoordinateComplex_hasTemperateGrowth j)
      (weightedFrequencyCoordinate_hasTemperateGrowth δ i)
      (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ))
  rw [hterms] at hmul
  rw [map_zero] at hmul
  exact hmul

/-- A weakly divergence-free `L²` field annihilates the regularized
frequency-weighted divergence multiplier. -/
theorem weakDivFreeL2_regularizedFrequencyDivergence_zero {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (δ : ℝ) (i : Fin 3) :
    ∑ j : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ : L2Vec3 => Complex.ofReal
        (regularizedFrequencyCoord δ i ξ * regularizedFrequencyCoord δ j ξ *
          regularizedFrequencyWeight δ ξ))
      (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) = 0 := by
  change MemLp a (2 : ℝ≥0∞) volume ∧ _ at ha
  let c : ℂ := Complex.ofReal (δ⁻¹ * δ⁻¹)
  have h := weakDivFreeL2_weightedFrequencyDivergence_zero ha δ i
  have hscaled := congrArg (fun z : 𝓢'(L2Vec3, ℂ) => c • z) h
  simp only [Finset.smul_sum] at hscaled
  have hc0 : c • (0 : 𝓢'(L2Vec3, ℂ)) = 0 :=
    smul_zero (M := ℂ) (A := 𝓢'(L2Vec3, ℂ)) c
  rw [hc0] at hscaled
  have hterms : ∑ j : Fin 3,
      c • TemperedDistribution.fourierMultiplierCLM ℂ
        (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i)
        (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) =
      ∑ j : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : L2Vec3 => Complex.ofReal
          (regularizedFrequencyCoord δ i ξ * regularizedFrequencyCoord δ j ξ *
            regularizedFrequencyWeight δ ξ))
        (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hsmul := TemperedDistribution.fourierMultiplierCLM_smul (F := ℂ) (E := L2Vec3)
      (frequencyCoordinateComplex_hasTemperateGrowth j |>.mul
        (weightedFrequencyCoordinate_hasTemperateGrowth δ i)) c
    have hsmul' := congrArg
      (fun L : 𝓢'(L2Vec3, ℂ) →L[ℂ] 𝓢'(L2Vec3, ℂ) =>
        L (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ))) hsmul
    have hsmul'' : TemperedDistribution.fourierMultiplierCLM ℂ
        (c • (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i))
        (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) =
      c • TemperedDistribution.fourierMultiplierCLM ℂ
        (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i)
        (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) := by
      simpa using hsmul'
    have hfun : c • (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i) =
        (fun ξ : L2Vec3 => Complex.ofReal
          (regularizedFrequencyCoord δ i ξ * regularizedFrequencyCoord δ j ξ *
            regularizedFrequencyWeight δ ξ)) := by
      funext ξ
      simp [c, frequencyCoordinateComplex, weightedFrequencyCoordinate,
        regularizedWeightComplex, regularizedFrequencyCoord, frequencyL2Coord,
        PiLp.proj_apply, Complex.ofReal_mul]
      ring
    calc
      c • TemperedDistribution.fourierMultiplierCLM ℂ
          (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i)
          (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) =
        TemperedDistribution.fourierMultiplierCLM ℂ
          (c • (frequencyCoordinateComplex j * weightedFrequencyCoordinate δ i))
          (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) := hsmul''.symm
      _ = TemperedDistribution.fourierMultiplierCLM ℂ
          (fun ξ : L2Vec3 => Complex.ofReal
            (regularizedFrequencyCoord δ i ξ * regularizedFrequencyCoord δ j ξ *
              regularizedFrequencyWeight δ ξ))
          (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ)) := by
        exact congrArg (fun g : L2Vec3 → ℂ =>
          TemperedDistribution.fourierMultiplierCLM ℂ g
            (weakFieldFourierComponent ha.1 j : 𝓢'(L2Vec3, ℂ))) hfun
  rw [hterms] at hscaled
  exact hscaled

/-- Taking real parts of the complex regularized curl recovers the real
regularized curl on the spatial carrier. -/
theorem regularizedPotentialCurlComponentLp_real_eq
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) :
    (fun y : L2Vec3 => Complex.re (regularizedPotentialCurlComponentLp ha δ hδ i y)) =ᵐ[volume]
      (fun y : L2Vec3 => regularizedPotentialCurl ha δ hδ (WithLp.ofLp y) i) := by
  fin_cases i
  · filter_upwards [Lp.coeFn_sub
      (regularizedPotentialDerivativeComponentLp ha δ hδ 2 1)
      (regularizedPotentialDerivativeComponentLp ha δ hδ 1 2)] with y hy
    simpa [regularizedPotentialCurlComponentLp, regularizedPotentialCurl,
      regularizedPotentialGradientVec3, curlOfGradient,
      regularizedPotentialDerivativeComponentLp, Complex.sub_re] using congrArg Complex.re hy
  · filter_upwards [Lp.coeFn_sub
      (regularizedPotentialDerivativeComponentLp ha δ hδ 0 2)
      (regularizedPotentialDerivativeComponentLp ha δ hδ 2 0)] with y hy
    simpa [regularizedPotentialCurlComponentLp, regularizedPotentialCurl,
      regularizedPotentialGradientVec3, curlOfGradient,
      regularizedPotentialDerivativeComponentLp, Complex.sub_re] using congrArg Complex.re hy
  · filter_upwards [Lp.coeFn_sub
      (regularizedPotentialDerivativeComponentLp ha δ hδ 1 0)
      (regularizedPotentialDerivativeComponentLp ha δ hδ 0 1)] with y hy
    simpa [regularizedPotentialCurlComponentLp, regularizedPotentialCurl,
      regularizedPotentialGradientVec3, curlOfGradient,
      regularizedPotentialDerivativeComponentLp, Complex.sub_re] using congrArg Complex.re hy

end CKN

end
